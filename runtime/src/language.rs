//! Core language traits and types for MeTTaIL
//!
//! These types are shared between the macro-generated code and the REPL.

use std::any::Any;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::LanguageMetadata;

/// Seed facts for pre-populating Ascent relations before fixpoint.
///
/// Keys are relation names (e.g., `"certified"`), values are tuples
/// represented as string vectors (e.g., `vec![vec!["item_A"]]`).
/// The codegen parses each string into the relation's parameter type
/// at runtime.
pub type SeedFacts = HashMap<String, Vec<Vec<String>>>;

/// Exact observational key for a term in an extracted rewrite graph.
///
/// Generated languages populate this from their semantic hash write stream,
/// not from a fixed-width digest. Legacy/manual result graphs may leave it
/// absent, in which case traversal falls back to `term_id`.
pub type ExactTermKey = Vec<u8>;

/// Runtime seed id plus display text and priority weight.
///
/// Lower weights are explored first by weighted prefix traversal. The display
/// component is diagnostic only; it must not be used as an equivalence key.
pub type WeightedSeedId = (u64, String, f64);

/// Runtime backend selected for a language evaluation.
///
/// `Ascent` is the legacy/reference rewrite backend. `Dovetail` and
/// `RhoMachine` are explicit targets so user-facing execution can be routed by a
/// verified flip gate instead of hard-coding Ascent forever.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeBackend {
    Ascent,
    Dovetail,
    RhoMachine,
}

impl fmt::Display for RuntimeBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeBackend::Ascent => write!(f, "Ascent"),
            RuntimeBackend::Dovetail => write!(f, "Dovetail"),
            RuntimeBackend::RhoMachine => write!(f, "RhoMachine"),
        }
    }
}

/// Executable runtime backend capability for a concrete `Language` value.
///
/// Static generated metadata uses [`crate::BackendCapabilityDef`]. This owned
/// form is the runtime view: wrappers can add checked backends without mutating
/// generated static metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeBackendCapability {
    pub backend: RuntimeBackend,
    pub is_default: bool,
}

impl RuntimeBackendCapability {
    pub fn from_static(capability: &crate::BackendCapabilityDef) -> Self {
        Self {
            backend: capability.backend,
            is_default: capability.is_default,
        }
    }
}

/// Executable artifact boundary used by a runtime backend report.
///
/// This is deliberately substrate-neutral. `RhoNormalizedAst` corresponds to a
/// direct `rhoapi::Par` value, not Rholang source text; `RhoBytecode` is the
/// forward-compatible execution artifact for the planned bytecode path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeBackendArtifact {
    /// Legacy/reference Ascent fixpoint facts.
    AscentFixpoint,
    /// Dovetail's checked, substrate-neutral rewrite report.
    DovetailRunReport,
    /// Normalized Rholang AST (`rhoapi::Par`) injected directly into RhoRuntime.
    RhoNormalizedAst,
    /// Rholang bytecode artifact, once the host runtime exposes bytecode.
    RhoBytecode,
}

impl fmt::Display for RuntimeBackendArtifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeBackendArtifact::AscentFixpoint => write!(f, "AscentFixpoint"),
            RuntimeBackendArtifact::DovetailRunReport => write!(f, "DovetailRunReport"),
            RuntimeBackendArtifact::RhoNormalizedAst => write!(f, "RhoNormalizedAst"),
            RuntimeBackendArtifact::RhoBytecode => write!(f, "RhoBytecode"),
        }
    }
}

/// Ground observation value returned by a non-Ascent runtime backend.
#[non_exhaustive]
pub enum RuntimeObservationValue {
    Int(i64),
    Bool(bool),
    Text(String),
    TermDisplay(String),
    Bytes(Vec<u8>),
    Uri(String),
    DoubleBits(u64),
    BigIntBytes(Vec<u8>),
    BigRationalBytes {
        numerator: Vec<u8>,
        denominator: Vec<u8>,
    },
    FixedPointBytes {
        unscaled: Vec<u8>,
        scale: u32,
    },
    PrivateName(Vec<u8>),
    DeployId(Vec<u8>),
    DeployerId(Vec<u8>),
    SysAuthToken,
    List(Vec<RuntimeObservationValue>),
    Tuple(Vec<RuntimeObservationValue>),
    Set(Vec<RuntimeObservationValue>),
    Map(Vec<(RuntimeObservationValue, RuntimeObservationValue)>),
    Bag(Vec<(RuntimeObservationValue, usize)>),
    /// A structurally-decoded reflected constructor term: a constructor label
    /// applied to already-decoded child observations, in constructor-argument
    /// order. This is the decoded image of the Rho constructor-reflection ABI
    /// `EList[GPrivate("mettail.term.{fingerprint}.{label}"), children…]` emitted
    /// by a base rewrite's σ-receiver (see the codegen `reflect_ground_term_par` /
    /// the runtime `decode_reflected_term`). Unlike the flat [`TermDisplay`], it
    /// preserves the full tree so a runtime observation can be compared for exact
    /// structural equality against a term's reflected normal form.
    Term {
        constructor: String,
        children: Vec<RuntimeObservationValue>,
    },
}

fn observation_variant_rank(value: &RuntimeObservationValue) -> u8 {
    match value {
        RuntimeObservationValue::Int(_) => 0,
        RuntimeObservationValue::Bool(_) => 1,
        RuntimeObservationValue::Text(_) => 2,
        RuntimeObservationValue::TermDisplay(_) => 3,
        RuntimeObservationValue::Bytes(_) => 4,
        RuntimeObservationValue::Uri(_) => 5,
        RuntimeObservationValue::DoubleBits(_) => 6,
        RuntimeObservationValue::BigIntBytes(_) => 7,
        RuntimeObservationValue::BigRationalBytes { .. } => 8,
        RuntimeObservationValue::FixedPointBytes { .. } => 9,
        RuntimeObservationValue::PrivateName(_) => 10,
        RuntimeObservationValue::DeployId(_) => 11,
        RuntimeObservationValue::DeployerId(_) => 12,
        RuntimeObservationValue::SysAuthToken => 13,
        RuntimeObservationValue::List(_) => 14,
        RuntimeObservationValue::Tuple(_) => 15,
        RuntimeObservationValue::Set(_) => 16,
        RuntimeObservationValue::Map(_) => 17,
        RuntimeObservationValue::Bag(_) => 18,
        RuntimeObservationValue::Term { .. } => 19,
    }
}

fn compare_observation_values(
    left_root: &RuntimeObservationValue,
    right_root: &RuntimeObservationValue,
) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    enum Work<'a> {
        Value(&'a RuntimeObservationValue, &'a RuntimeObservationValue),
        Values(&'a [RuntimeObservationValue], &'a [RuntimeObservationValue], usize),
        Map(
            &'a [(RuntimeObservationValue, RuntimeObservationValue)],
            &'a [(RuntimeObservationValue, RuntimeObservationValue)],
            usize,
        ),
        Bag(
            &'a [(RuntimeObservationValue, usize)],
            &'a [(RuntimeObservationValue, usize)],
            usize,
        ),
        Count(usize, usize),
    }

    let mut work = vec![Work::Value(left_root, right_root)];
    while let Some(step) = work.pop() {
        match step {
            Work::Value(left, right) => {
                let ordering = observation_variant_rank(left).cmp(&observation_variant_rank(right));
                if ordering != Ordering::Equal {
                    return ordering;
                }
                match (left, right) {
                    (RuntimeObservationValue::Int(left), RuntimeObservationValue::Int(right)) => {
                        if left != right {
                            return left.cmp(right);
                        }
                    },
                    (RuntimeObservationValue::Bool(left), RuntimeObservationValue::Bool(right)) => {
                        if left != right {
                            return left.cmp(right);
                        }
                    },
                    (RuntimeObservationValue::Text(left), RuntimeObservationValue::Text(right))
                    | (
                        RuntimeObservationValue::TermDisplay(left),
                        RuntimeObservationValue::TermDisplay(right),
                    )
                    | (RuntimeObservationValue::Uri(left), RuntimeObservationValue::Uri(right)) => {
                        if left != right {
                            return left.cmp(right);
                        }
                    },
                    (
                        RuntimeObservationValue::Bytes(left),
                        RuntimeObservationValue::Bytes(right),
                    )
                    | (
                        RuntimeObservationValue::BigIntBytes(left),
                        RuntimeObservationValue::BigIntBytes(right),
                    )
                    | (
                        RuntimeObservationValue::PrivateName(left),
                        RuntimeObservationValue::PrivateName(right),
                    )
                    | (
                        RuntimeObservationValue::DeployId(left),
                        RuntimeObservationValue::DeployId(right),
                    )
                    | (
                        RuntimeObservationValue::DeployerId(left),
                        RuntimeObservationValue::DeployerId(right),
                    ) => {
                        if left != right {
                            return left.cmp(right);
                        }
                    },
                    (
                        RuntimeObservationValue::DoubleBits(left),
                        RuntimeObservationValue::DoubleBits(right),
                    ) => {
                        if left != right {
                            return left.cmp(right);
                        }
                    },
                    (
                        RuntimeObservationValue::BigRationalBytes {
                            numerator: left_numerator,
                            denominator: left_denominator,
                        },
                        RuntimeObservationValue::BigRationalBytes {
                            numerator: right_numerator,
                            denominator: right_denominator,
                        },
                    ) => {
                        let ordering = left_numerator.cmp(right_numerator);
                        if ordering != Ordering::Equal {
                            return ordering;
                        }
                        let ordering = left_denominator.cmp(right_denominator);
                        if ordering != Ordering::Equal {
                            return ordering;
                        }
                    },
                    (
                        RuntimeObservationValue::FixedPointBytes {
                            unscaled: left_unscaled,
                            scale: left_scale,
                        },
                        RuntimeObservationValue::FixedPointBytes {
                            unscaled: right_unscaled,
                            scale: right_scale,
                        },
                    ) => {
                        let ordering = left_unscaled.cmp(right_unscaled);
                        if ordering != Ordering::Equal {
                            return ordering;
                        }
                        if left_scale != right_scale {
                            return left_scale.cmp(right_scale);
                        }
                    },
                    (
                        RuntimeObservationValue::SysAuthToken,
                        RuntimeObservationValue::SysAuthToken,
                    ) => {},
                    (RuntimeObservationValue::List(left), RuntimeObservationValue::List(right))
                    | (
                        RuntimeObservationValue::Tuple(left),
                        RuntimeObservationValue::Tuple(right),
                    )
                    | (RuntimeObservationValue::Set(left), RuntimeObservationValue::Set(right)) => {
                        work.push(Work::Values(left, right, 0));
                    },
                    (RuntimeObservationValue::Map(left), RuntimeObservationValue::Map(right)) => {
                        work.push(Work::Map(left, right, 0));
                    },
                    (RuntimeObservationValue::Bag(left), RuntimeObservationValue::Bag(right)) => {
                        work.push(Work::Bag(left, right, 0));
                    },
                    (
                        RuntimeObservationValue::Term {
                            constructor: left_constructor,
                            children: left_children,
                        },
                        RuntimeObservationValue::Term {
                            constructor: right_constructor,
                            children: right_children,
                        },
                    ) => {
                        let ordering = left_constructor.cmp(right_constructor);
                        if ordering != Ordering::Equal {
                            return ordering;
                        }
                        work.push(Work::Values(left_children, right_children, 0));
                    },
                    _ => unreachable!("equal observation variant ranks must have equal variants"),
                }
            },
            Work::Values(left, right, index) => {
                let shared_len = left.len().min(right.len());
                if index == shared_len {
                    let ordering = left.len().cmp(&right.len());
                    if ordering != Ordering::Equal {
                        return ordering;
                    }
                } else {
                    work.push(Work::Values(left, right, index + 1));
                    work.push(Work::Value(&left[index], &right[index]));
                }
            },
            Work::Map(left, right, index) => {
                let shared_len = left.len().min(right.len());
                if index == shared_len {
                    let ordering = left.len().cmp(&right.len());
                    if ordering != Ordering::Equal {
                        return ordering;
                    }
                } else {
                    work.push(Work::Map(left, right, index + 1));
                    work.push(Work::Value(&left[index].1, &right[index].1));
                    work.push(Work::Value(&left[index].0, &right[index].0));
                }
            },
            Work::Bag(left, right, index) => {
                let shared_len = left.len().min(right.len());
                if index == shared_len {
                    let ordering = left.len().cmp(&right.len());
                    if ordering != Ordering::Equal {
                        return ordering;
                    }
                } else {
                    work.push(Work::Bag(left, right, index + 1));
                    work.push(Work::Count(left[index].1, right[index].1));
                    work.push(Work::Value(&left[index].0, &right[index].0));
                }
            },
            Work::Count(left, right) => {
                if left != right {
                    return left.cmp(&right);
                }
            },
        }
    }
    Ordering::Equal
}

impl PartialEq for RuntimeObservationValue {
    fn eq(&self, other: &Self) -> bool {
        compare_observation_values(self, other).is_eq()
    }
}

impl Eq for RuntimeObservationValue {}

impl PartialOrd for RuntimeObservationValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(compare_observation_values(self, other))
    }
}

impl Ord for RuntimeObservationValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare_observation_values(self, other)
    }
}

impl std::hash::Hash for RuntimeObservationValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        enum Work<'a> {
            Value(&'a RuntimeObservationValue),
            Values(&'a [RuntimeObservationValue], usize),
            Map(&'a [(RuntimeObservationValue, RuntimeObservationValue)], usize),
            Bag(&'a [(RuntimeObservationValue, usize)], usize),
            Count(usize),
        }

        let mut work = vec![Work::Value(self)];
        while let Some(step) = work.pop() {
            match step {
                Work::Value(value) => {
                    std::mem::discriminant(value).hash(state);
                    match value {
                        RuntimeObservationValue::Int(value) => value.hash(state),
                        RuntimeObservationValue::Bool(value) => value.hash(state),
                        RuntimeObservationValue::Text(value)
                        | RuntimeObservationValue::TermDisplay(value)
                        | RuntimeObservationValue::Uri(value) => value.hash(state),
                        RuntimeObservationValue::Bytes(value)
                        | RuntimeObservationValue::BigIntBytes(value)
                        | RuntimeObservationValue::PrivateName(value)
                        | RuntimeObservationValue::DeployId(value)
                        | RuntimeObservationValue::DeployerId(value) => value.hash(state),
                        RuntimeObservationValue::DoubleBits(value) => value.hash(state),
                        RuntimeObservationValue::BigRationalBytes { numerator, denominator } => {
                            numerator.hash(state);
                            denominator.hash(state);
                        },
                        RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                            unscaled.hash(state);
                            scale.hash(state);
                        },
                        RuntimeObservationValue::SysAuthToken => {},
                        RuntimeObservationValue::List(children)
                        | RuntimeObservationValue::Tuple(children)
                        | RuntimeObservationValue::Set(children) => {
                            children.len().hash(state);
                            work.push(Work::Values(children, 0));
                        },
                        RuntimeObservationValue::Map(entries) => {
                            entries.len().hash(state);
                            work.push(Work::Map(entries, 0));
                        },
                        RuntimeObservationValue::Bag(entries) => {
                            entries.len().hash(state);
                            work.push(Work::Bag(entries, 0));
                        },
                        RuntimeObservationValue::Term { constructor, children } => {
                            constructor.hash(state);
                            children.len().hash(state);
                            work.push(Work::Values(children, 0));
                        },
                    }
                },
                Work::Values(values, index) => {
                    if index < values.len() {
                        work.push(Work::Values(values, index + 1));
                        work.push(Work::Value(&values[index]));
                    }
                },
                Work::Map(entries, index) => {
                    if index < entries.len() {
                        work.push(Work::Map(entries, index + 1));
                        work.push(Work::Value(&entries[index].1));
                        work.push(Work::Value(&entries[index].0));
                    }
                },
                Work::Bag(entries, index) => {
                    if index < entries.len() {
                        work.push(Work::Bag(entries, index + 1));
                        work.push(Work::Count(entries[index].1));
                        work.push(Work::Value(&entries[index].0));
                    }
                },
                Work::Count(count) => count.hash(state),
            }
        }
    }
}

impl Clone for RuntimeObservationValue {
    fn clone(&self) -> Self {
        #[derive(Clone, Copy)]
        enum Build<'a> {
            List(usize),
            Tuple(usize),
            Set(usize),
            Map(usize),
            Bag(&'a [(RuntimeObservationValue, usize)]),
            Term { constructor: &'a str, arity: usize },
        }

        enum Work<'a> {
            Visit(&'a RuntimeObservationValue),
            Build(Build<'a>),
        }

        let mut work = vec![Work::Visit(self)];
        let mut values = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Work::Visit(value) => match value {
                    RuntimeObservationValue::Int(value) => {
                        values.push(RuntimeObservationValue::Int(*value))
                    },
                    RuntimeObservationValue::Bool(value) => {
                        values.push(RuntimeObservationValue::Bool(*value))
                    },
                    RuntimeObservationValue::Text(value) => {
                        values.push(RuntimeObservationValue::Text(value.clone()))
                    },
                    RuntimeObservationValue::TermDisplay(value) => {
                        values.push(RuntimeObservationValue::TermDisplay(value.clone()))
                    },
                    RuntimeObservationValue::Bytes(value) => {
                        values.push(RuntimeObservationValue::Bytes(value.clone()))
                    },
                    RuntimeObservationValue::Uri(value) => {
                        values.push(RuntimeObservationValue::Uri(value.clone()))
                    },
                    RuntimeObservationValue::DoubleBits(value) => {
                        values.push(RuntimeObservationValue::DoubleBits(*value))
                    },
                    RuntimeObservationValue::BigIntBytes(value) => {
                        values.push(RuntimeObservationValue::BigIntBytes(value.clone()))
                    },
                    RuntimeObservationValue::BigRationalBytes { numerator, denominator } => values
                        .push(RuntimeObservationValue::BigRationalBytes {
                            numerator: numerator.clone(),
                            denominator: denominator.clone(),
                        }),
                    RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                        values.push(RuntimeObservationValue::FixedPointBytes {
                            unscaled: unscaled.clone(),
                            scale: *scale,
                        })
                    },
                    RuntimeObservationValue::PrivateName(value) => {
                        values.push(RuntimeObservationValue::PrivateName(value.clone()))
                    },
                    RuntimeObservationValue::DeployId(value) => {
                        values.push(RuntimeObservationValue::DeployId(value.clone()))
                    },
                    RuntimeObservationValue::DeployerId(value) => {
                        values.push(RuntimeObservationValue::DeployerId(value.clone()))
                    },
                    RuntimeObservationValue::SysAuthToken => {
                        values.push(RuntimeObservationValue::SysAuthToken)
                    },
                    RuntimeObservationValue::List(children) => {
                        work.push(Work::Build(Build::List(children.len())));
                        work.extend(children.iter().rev().map(Work::Visit));
                    },
                    RuntimeObservationValue::Tuple(children) => {
                        work.push(Work::Build(Build::Tuple(children.len())));
                        work.extend(children.iter().rev().map(Work::Visit));
                    },
                    RuntimeObservationValue::Set(children) => {
                        work.push(Work::Build(Build::Set(children.len())));
                        work.extend(children.iter().rev().map(Work::Visit));
                    },
                    RuntimeObservationValue::Map(entries) => {
                        work.push(Work::Build(Build::Map(entries.len())));
                        for (key, value) in entries.iter().rev() {
                            work.push(Work::Visit(value));
                            work.push(Work::Visit(key));
                        }
                    },
                    RuntimeObservationValue::Bag(entries) => {
                        work.push(Work::Build(Build::Bag(entries)));
                        work.extend(entries.iter().rev().map(|(value, _)| Work::Visit(value)));
                    },
                    RuntimeObservationValue::Term { constructor, children } => {
                        work.push(Work::Build(Build::Term { constructor, arity: children.len() }));
                        work.extend(children.iter().rev().map(Work::Visit));
                    },
                },
                Work::Build(build) => {
                    let arity = match build {
                        Build::List(arity)
                        | Build::Tuple(arity)
                        | Build::Set(arity)
                        | Build::Map(arity)
                        | Build::Term { arity, .. } => arity,
                        Build::Bag(entries) => entries.len(),
                    };
                    let value_arity = if matches!(build, Build::Map(_)) {
                        arity * 2
                    } else {
                        arity
                    };
                    let split = values
                        .len()
                        .checked_sub(value_arity)
                        .expect("observation clone PDA: continuation underflow");
                    let children = values.split_off(split);
                    let value = match build {
                        Build::List(_) => RuntimeObservationValue::List(children),
                        Build::Tuple(_) => RuntimeObservationValue::Tuple(children),
                        Build::Set(_) => RuntimeObservationValue::Set(children),
                        Build::Map(_) => {
                            let mut children = children.into_iter();
                            let mut entries = Vec::with_capacity(arity);
                            while let Some(key) = children.next() {
                                let value = children
                                    .next()
                                    .expect("observation clone PDA: map value is missing");
                                entries.push((key, value));
                            }
                            RuntimeObservationValue::Map(entries)
                        },
                        Build::Bag(entries) => RuntimeObservationValue::Bag(
                            children
                                .into_iter()
                                .zip(entries.iter().map(|(_, count)| *count))
                                .collect(),
                        ),
                        Build::Term { constructor, .. } => RuntimeObservationValue::Term {
                            constructor: constructor.to_owned(),
                            children,
                        },
                    };
                    values.push(value);
                },
            }
        }

        assert_eq!(
            values.len(),
            1,
            "observation clone PDA: final value stack must contain one result"
        );
        values
            .pop()
            .expect("observation clone PDA: missing root value")
    }
}

impl Drop for RuntimeObservationValue {
    fn drop(&mut self) {
        fn move_children_to(
            value: &mut RuntimeObservationValue,
            work: &mut Vec<RuntimeObservationValue>,
        ) {
            match value {
                RuntimeObservationValue::List(children)
                | RuntimeObservationValue::Tuple(children)
                | RuntimeObservationValue::Set(children)
                | RuntimeObservationValue::Term { children, .. } => work.append(children),
                RuntimeObservationValue::Map(entries) => {
                    for (key, value) in std::mem::take(entries) {
                        work.push(key);
                        work.push(value);
                    }
                },
                RuntimeObservationValue::Bag(entries) => {
                    work.extend(std::mem::take(entries).into_iter().map(|(value, _)| value));
                },
                _ => {},
            }
        }

        let mut work = Vec::new();
        move_children_to(self, &mut work);
        while let Some(mut value) = work.pop() {
            move_children_to(&mut value, &mut work);
            // `value` now contains no recursive children, so its automatic call back into this
            // destructor is constant-stack and performs no allocation.
        }
    }
}

impl fmt::Display for RuntimeObservationValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Work<'a> {
            Value(&'a RuntimeObservationValue),
            Text(&'static str),
            Count(usize),
        }

        fn push_sequence<'a>(
            work: &mut Vec<Work<'a>>,
            values: &'a [RuntimeObservationValue],
            close: &'static str,
        ) {
            work.push(Work::Text(close));
            for (index, value) in values.iter().enumerate().rev() {
                work.push(Work::Value(value));
                if index > 0 {
                    work.push(Work::Text(", "));
                }
            }
        }

        fn write_hex(f: &mut fmt::Formatter<'_>, bytes: &[u8]) -> fmt::Result {
            for byte in bytes {
                write!(f, "{byte:02x}")?;
            }
            Ok(())
        }

        let mut work = vec![Work::Value(self)];
        while let Some(step) = work.pop() {
            match step {
                Work::Text(text) => f.write_str(text)?,
                Work::Count(count) => write!(f, "{count}")?,
                Work::Value(value) => match value {
                    RuntimeObservationValue::Int(value) => write!(f, "{value}")?,
                    RuntimeObservationValue::Bool(value) => write!(f, "{value}")?,
                    RuntimeObservationValue::Text(value) => write!(f, "{value:?}")?,
                    RuntimeObservationValue::TermDisplay(value) => f.write_str(value)?,
                    RuntimeObservationValue::Bytes(value) => {
                        f.write_str("0x")?;
                        write_hex(f, value)?;
                    },
                    RuntimeObservationValue::Uri(value) => write!(f, "Uri({value:?})")?,
                    RuntimeObservationValue::DoubleBits(value) => {
                        write!(f, "DoubleBits(0x{value:016x})")?
                    },
                    RuntimeObservationValue::BigIntBytes(value) => {
                        f.write_str("BigInt(0x")?;
                        write_hex(f, value)?;
                        f.write_str(")")?;
                    },
                    RuntimeObservationValue::BigRationalBytes { numerator, denominator } => {
                        f.write_str("BigRat(0x")?;
                        write_hex(f, numerator)?;
                        f.write_str("/0x")?;
                        write_hex(f, denominator)?;
                        f.write_str(")")?;
                    },
                    RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                        f.write_str("FixedPoint(0x")?;
                        write_hex(f, unscaled)?;
                        write!(f, " scale {scale})")?;
                    },
                    RuntimeObservationValue::PrivateName(value) => {
                        f.write_str("Private(0x")?;
                        write_hex(f, value)?;
                        f.write_str(")")?;
                    },
                    RuntimeObservationValue::DeployId(value) => {
                        f.write_str("DeployId(0x")?;
                        write_hex(f, value)?;
                        f.write_str(")")?;
                    },
                    RuntimeObservationValue::DeployerId(value) => {
                        f.write_str("DeployerId(0x")?;
                        write_hex(f, value)?;
                        f.write_str(")")?;
                    },
                    RuntimeObservationValue::SysAuthToken => f.write_str("SysAuthToken")?,
                    RuntimeObservationValue::List(values) => {
                        f.write_str("[")?;
                        push_sequence(&mut work, values, "]");
                    },
                    RuntimeObservationValue::Tuple(values) => {
                        f.write_str("(")?;
                        push_sequence(&mut work, values, ")");
                    },
                    RuntimeObservationValue::Set(values) => {
                        f.write_str("Set{")?;
                        push_sequence(&mut work, values, "}");
                    },
                    RuntimeObservationValue::Map(entries) => {
                        f.write_str("{")?;
                        work.push(Work::Text("}"));
                        for (index, (key, value)) in entries.iter().enumerate().rev() {
                            work.push(Work::Value(value));
                            work.push(Work::Text(": "));
                            work.push(Work::Value(key));
                            if index > 0 {
                                work.push(Work::Text(", "));
                            }
                        }
                    },
                    RuntimeObservationValue::Bag(entries) => {
                        f.write_str("Bag{")?;
                        work.push(Work::Text("}"));
                        for (index, (value, count)) in entries.iter().enumerate().rev() {
                            work.push(Work::Count(*count));
                            work.push(Work::Text(" * "));
                            work.push(Work::Value(value));
                            if index > 0 {
                                work.push(Work::Text(", "));
                            }
                        }
                    },
                    RuntimeObservationValue::Term { constructor, children } => {
                        f.write_str(constructor)?;
                        if !children.is_empty() {
                            f.write_str("(")?;
                            push_sequence(&mut work, children, ")");
                        }
                    },
                },
            }
        }
        Ok(())
    }
}

impl fmt::Debug for RuntimeObservationValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return fmt_observation_debug_pretty(self, f);
        }

        enum Work<'a> {
            Value(&'a RuntimeObservationValue),
            Text(&'static str),
            Count(usize),
        }

        fn push_values<'a>(
            work: &mut Vec<Work<'a>>,
            values: &'a [RuntimeObservationValue],
            close: &'static str,
        ) {
            work.push(Work::Text(close));
            for (index, value) in values.iter().enumerate().rev() {
                work.push(Work::Value(value));
                if index > 0 {
                    work.push(Work::Text(", "));
                }
            }
        }

        let mut work = vec![Work::Value(self)];
        while let Some(step) = work.pop() {
            match step {
                Work::Text(text) => f.write_str(text)?,
                Work::Count(count) => write!(f, "{count:?}")?,
                Work::Value(value) => match value {
                    RuntimeObservationValue::Int(value) => write!(f, "Int({value:?})")?,
                    RuntimeObservationValue::Bool(value) => write!(f, "Bool({value:?})")?,
                    RuntimeObservationValue::Text(value) => write!(f, "Text({value:?})")?,
                    RuntimeObservationValue::TermDisplay(value) => {
                        write!(f, "TermDisplay({value:?})")?
                    },
                    RuntimeObservationValue::Bytes(value) => write!(f, "Bytes({value:?})")?,
                    RuntimeObservationValue::Uri(value) => write!(f, "Uri({value:?})")?,
                    RuntimeObservationValue::DoubleBits(value) => {
                        write!(f, "DoubleBits({value:?})")?
                    },
                    RuntimeObservationValue::BigIntBytes(value) => {
                        write!(f, "BigIntBytes({value:?})")?
                    },
                    RuntimeObservationValue::BigRationalBytes { numerator, denominator } => {
                        write!(
                            f,
                            "BigRationalBytes {{ numerator: {numerator:?}, denominator: {denominator:?} }}"
                        )?
                    },
                    RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                        write!(
                            f,
                            "FixedPointBytes {{ unscaled: {unscaled:?}, scale: {scale:?} }}"
                        )?
                    },
                    RuntimeObservationValue::PrivateName(value) => {
                        write!(f, "PrivateName({value:?})")?
                    },
                    RuntimeObservationValue::DeployId(value) => {
                        write!(f, "DeployId({value:?})")?
                    },
                    RuntimeObservationValue::DeployerId(value) => {
                        write!(f, "DeployerId({value:?})")?
                    },
                    RuntimeObservationValue::SysAuthToken => f.write_str("SysAuthToken")?,
                    RuntimeObservationValue::List(values) => {
                        f.write_str("List([")?;
                        push_values(&mut work, values, "])");
                    },
                    RuntimeObservationValue::Tuple(values) => {
                        f.write_str("Tuple([")?;
                        push_values(&mut work, values, "])");
                    },
                    RuntimeObservationValue::Set(values) => {
                        f.write_str("Set([")?;
                        push_values(&mut work, values, "])");
                    },
                    RuntimeObservationValue::Map(entries) => {
                        f.write_str("Map([")?;
                        work.push(Work::Text("])") );
                        for (index, (key, value)) in entries.iter().enumerate().rev() {
                            work.push(Work::Text(")"));
                            work.push(Work::Value(value));
                            work.push(Work::Text(", "));
                            work.push(Work::Value(key));
                            work.push(Work::Text("("));
                            if index > 0 {
                                work.push(Work::Text(", "));
                            }
                        }
                    },
                    RuntimeObservationValue::Bag(entries) => {
                        f.write_str("Bag([")?;
                        work.push(Work::Text("])") );
                        for (index, (value, count)) in entries.iter().enumerate().rev() {
                            work.push(Work::Text(")"));
                            work.push(Work::Count(*count));
                            work.push(Work::Text(", "));
                            work.push(Work::Value(value));
                            work.push(Work::Text("("));
                            if index > 0 {
                                work.push(Work::Text(", "));
                            }
                        }
                    },
                    RuntimeObservationValue::Term { constructor, children } => {
                        write!(f, "Term {{ constructor: {constructor:?}, children: [")?;
                        push_values(&mut work, children, "] }");
                    },
                },
            }
        }
        Ok(())
    }
}

fn fmt_observation_debug_pretty(
    root: &RuntimeObservationValue,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    enum Work<'a> {
        Value(&'a RuntimeObservationValue, usize),
        Values(&'a [RuntimeObservationValue], usize),
        Map(&'a [(RuntimeObservationValue, RuntimeObservationValue)], usize),
        Bag(&'a [(RuntimeObservationValue, usize)], usize),
        Bytes(&'a [u8], usize),
        Text(&'static str),
        Indent(usize),
        String(&'a str),
        I64(i64),
        U64(u64),
        U32(u32),
        Usize(usize),
        Bool(bool),
    }

    fn push_tuple<'a>(work: &mut Vec<Work<'a>>, indent: usize, field: Work<'a>) {
        work.push(Work::Text(")"));
        work.push(Work::Indent(indent));
        work.push(Work::Text("\n"));
        work.push(Work::Text(","));
        work.push(field);
        work.push(Work::Indent(indent + 1));
    }

    fn push_struct_field<'a>(
        work: &mut Vec<Work<'a>>,
        indent: usize,
        name: &'static str,
        field: Work<'a>,
    ) {
        work.push(Work::Text("\n"));
        work.push(Work::Text(","));
        work.push(field);
        work.push(Work::Text(name));
        work.push(Work::Indent(indent));
    }

    let mut work = vec![Work::Value(root, 0)];
    while let Some(step) = work.pop() {
        match step {
            Work::Text(text) => f.write_str(text)?,
            Work::Indent(depth) => {
                for _ in 0..depth {
                    f.write_str("    ")?;
                }
            },
            Work::String(value) => write!(f, "{value:?}")?,
            Work::I64(value) => write!(f, "{value:?}")?,
            Work::U64(value) => write!(f, "{value:?}")?,
            Work::U32(value) => write!(f, "{value:?}")?,
            Work::Usize(value) => write!(f, "{value:?}")?,
            Work::Bool(value) => write!(f, "{value:?}")?,
            Work::Bytes(bytes, indent) => {
                if bytes.is_empty() {
                    f.write_str("[]")?;
                } else {
                    f.write_str("[\n")?;
                    work.push(Work::Text("]"));
                    work.push(Work::Indent(indent));
                    for byte in bytes.iter().rev() {
                        work.push(Work::Text(",\n"));
                        work.push(Work::U64(u64::from(*byte)));
                        work.push(Work::Indent(indent + 1));
                    }
                }
            },
            Work::Values(values, indent) => {
                if values.is_empty() {
                    f.write_str("[]")?;
                } else {
                    f.write_str("[\n")?;
                    work.push(Work::Text("]"));
                    work.push(Work::Indent(indent));
                    for value in values.iter().rev() {
                        work.push(Work::Text(",\n"));
                        work.push(Work::Value(value, indent + 1));
                        work.push(Work::Indent(indent + 1));
                    }
                }
            },
            Work::Map(entries, indent) => {
                if entries.is_empty() {
                    f.write_str("[]")?;
                } else {
                    f.write_str("[\n")?;
                    work.push(Work::Text("]"));
                    work.push(Work::Indent(indent));
                    for (key, value) in entries.iter().rev() {
                        work.push(Work::Text("),\n"));
                        work.push(Work::Indent(indent + 1));
                        work.push(Work::Text(",\n"));
                        work.push(Work::Value(value, indent + 2));
                        work.push(Work::Indent(indent + 2));
                        work.push(Work::Text(",\n"));
                        work.push(Work::Value(key, indent + 2));
                        work.push(Work::Indent(indent + 2));
                        work.push(Work::Text("(\n"));
                        work.push(Work::Indent(indent + 1));
                    }
                }
            },
            Work::Bag(entries, indent) => {
                if entries.is_empty() {
                    f.write_str("[]")?;
                } else {
                    f.write_str("[\n")?;
                    work.push(Work::Text("]"));
                    work.push(Work::Indent(indent));
                    for (value, count) in entries.iter().rev() {
                        work.push(Work::Text("),\n"));
                        work.push(Work::Indent(indent + 1));
                        work.push(Work::Text(",\n"));
                        work.push(Work::Usize(*count));
                        work.push(Work::Indent(indent + 2));
                        work.push(Work::Text(",\n"));
                        work.push(Work::Value(value, indent + 2));
                        work.push(Work::Indent(indent + 2));
                        work.push(Work::Text("(\n"));
                        work.push(Work::Indent(indent + 1));
                    }
                }
            },
            Work::Value(value, indent) => match value {
                RuntimeObservationValue::Int(value) => {
                    f.write_str("Int(\n")?;
                    push_tuple(&mut work, indent, Work::I64(*value));
                },
                RuntimeObservationValue::Bool(value) => {
                    f.write_str("Bool(\n")?;
                    push_tuple(&mut work, indent, Work::Bool(*value));
                },
                RuntimeObservationValue::Text(value) => {
                    f.write_str("Text(\n")?;
                    push_tuple(&mut work, indent, Work::String(value));
                },
                RuntimeObservationValue::TermDisplay(value) => {
                    f.write_str("TermDisplay(\n")?;
                    push_tuple(&mut work, indent, Work::String(value));
                },
                RuntimeObservationValue::Bytes(value) => {
                    f.write_str("Bytes(\n")?;
                    push_tuple(&mut work, indent, Work::Bytes(value, indent + 1));
                },
                RuntimeObservationValue::Uri(value) => {
                    f.write_str("Uri(\n")?;
                    push_tuple(&mut work, indent, Work::String(value));
                },
                RuntimeObservationValue::DoubleBits(value) => {
                    f.write_str("DoubleBits(\n")?;
                    push_tuple(&mut work, indent, Work::U64(*value));
                },
                RuntimeObservationValue::BigIntBytes(value) => {
                    f.write_str("BigIntBytes(\n")?;
                    push_tuple(&mut work, indent, Work::Bytes(value, indent + 1));
                },
                RuntimeObservationValue::BigRationalBytes { numerator, denominator } => {
                    f.write_str("BigRationalBytes {\n")?;
                    work.push(Work::Text("}"));
                    work.push(Work::Indent(indent));
                    push_struct_field(
                        &mut work,
                        indent + 1,
                        "denominator: ",
                        Work::Bytes(denominator, indent + 1),
                    );
                    push_struct_field(
                        &mut work,
                        indent + 1,
                        "numerator: ",
                        Work::Bytes(numerator, indent + 1),
                    );
                },
                RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                    f.write_str("FixedPointBytes {\n")?;
                    work.push(Work::Text("}"));
                    work.push(Work::Indent(indent));
                    push_struct_field(&mut work, indent + 1, "scale: ", Work::U32(*scale));
                    push_struct_field(
                        &mut work,
                        indent + 1,
                        "unscaled: ",
                        Work::Bytes(unscaled, indent + 1),
                    );
                },
                RuntimeObservationValue::PrivateName(value) => {
                    f.write_str("PrivateName(\n")?;
                    push_tuple(&mut work, indent, Work::Bytes(value, indent + 1));
                },
                RuntimeObservationValue::DeployId(value) => {
                    f.write_str("DeployId(\n")?;
                    push_tuple(&mut work, indent, Work::Bytes(value, indent + 1));
                },
                RuntimeObservationValue::DeployerId(value) => {
                    f.write_str("DeployerId(\n")?;
                    push_tuple(&mut work, indent, Work::Bytes(value, indent + 1));
                },
                RuntimeObservationValue::SysAuthToken => f.write_str("SysAuthToken")?,
                RuntimeObservationValue::List(values) => {
                    f.write_str("List(\n")?;
                    push_tuple(&mut work, indent, Work::Values(values, indent + 1));
                },
                RuntimeObservationValue::Tuple(values) => {
                    f.write_str("Tuple(\n")?;
                    push_tuple(&mut work, indent, Work::Values(values, indent + 1));
                },
                RuntimeObservationValue::Set(values) => {
                    f.write_str("Set(\n")?;
                    push_tuple(&mut work, indent, Work::Values(values, indent + 1));
                },
                RuntimeObservationValue::Map(entries) => {
                    f.write_str("Map(\n")?;
                    push_tuple(&mut work, indent, Work::Map(entries, indent + 1));
                },
                RuntimeObservationValue::Bag(entries) => {
                    f.write_str("Bag(\n")?;
                    push_tuple(&mut work, indent, Work::Bag(entries, indent + 1));
                },
                RuntimeObservationValue::Term { constructor, children } => {
                    f.write_str("Term {\n")?;
                    work.push(Work::Text("}"));
                    work.push(Work::Indent(indent));
                    push_struct_field(
                        &mut work,
                        indent + 1,
                        "children: ",
                        Work::Values(children, indent + 1),
                    );
                    push_struct_field(
                        &mut work,
                        indent + 1,
                        "constructor: ",
                        Work::String(constructor),
                    );
                },
            },
        }
    }
    Ok(())
}

/// Values observed on one runtime output channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeChannelObservation {
    pub channel: String,
    pub values: Vec<RuntimeObservationValue>,
}

impl RuntimeChannelObservation {
    pub fn new(channel: impl Into<String>, values: Vec<RuntimeObservationValue>) -> Self {
        Self { channel: channel.into(), values }
    }

    /// Number of values observed before any order-insensitive projection.
    pub fn observed_count(&self) -> usize {
        self.values.len()
    }

    /// Order-insensitive exact-membership fingerprint for set-semantics checks.
    pub fn membership_fingerprint(&self) -> BTreeSet<RuntimeObservationValue> {
        self.values.iter().cloned().collect()
    }

    /// Order-insensitive counted fingerprint for bag-sensitive checks.
    pub fn multiplicity_fingerprint(&self) -> BTreeMap<RuntimeObservationValue, usize> {
        self.values
            .iter()
            .cloned()
            .fold(BTreeMap::new(), |mut counts, value| {
                *counts.entry(value).or_insert(0) += 1;
                counts
            })
    }
}

/// Structural validation failure for an observation-shaped runtime report.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RuntimeObservationReportError {
    InvalidObservationBackend {
        backend: RuntimeBackend,
    },
    InvalidObservationArtifact {
        backend: RuntimeBackend,
        artifact: RuntimeBackendArtifact,
    },
}

impl fmt::Display for RuntimeObservationReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeObservationReportError::InvalidObservationBackend { backend } => {
                write!(f, "observation-shaped output is not valid for backend {backend}")
            },
            RuntimeObservationReportError::InvalidObservationArtifact { backend, artifact } => {
                write!(
                    f,
                    "observation-shaped output for backend {backend} cannot use artifact {artifact}"
                )
            },
        }
    }
}

impl std::error::Error for RuntimeObservationReportError {}

/// Completeness status of a Dovetail runtime report projected into the generic
/// runtime layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeDovetailCompleteness {
    Complete,
    BoundedByCycleCut,
}

impl fmt::Display for RuntimeDovetailCompleteness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeDovetailCompleteness::Complete => write!(f, "Complete"),
            RuntimeDovetailCompleteness::BoundedByCycleCut => write!(f, "BoundedByCycleCut"),
        }
    }
}

/// One exact-keyed derivation node from a Dovetail report, projected into the
/// runtime-neutral report envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailTermRecord {
    pub ordinal: usize,
    pub class_id: u32,
    pub key: ExactTermKey,
    pub op_display: String,
    pub weight_display: String,
    pub is_root: bool,
    /// Reconstructed source-syntax rendering of this term (the inverse of the typed lowering, via
    /// the generated `build_<cat>_d` reconstructor + `Extractor`, then `format_term`). `None` when
    /// not reconstructed — production `exec` reports leave it `None`, byte-identical — or when the op
    /// is not structurally invertible. Reader-facing only; identity stays [`key`](Self::key).
    pub source_display: Option<String>,
}

/// Parent-to-child derivation edge from a Dovetail report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailDerivationEdge {
    pub ordinal: usize,
    pub parent_key: ExactTermKey,
    pub child_key: ExactTermKey,
    pub child_index: usize,
}

/// Aggregated labeled Dovetail rule firing evidence projected into the generic
/// runtime envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailRuleFiring {
    pub ordinal: usize,
    pub label: Option<String>,
    pub count: usize,
}

/// A σ sub-term surfaced in a runtime rewrite justification: a constructor label
/// applied to child sub-terms, in constructor-argument order.
///
/// This is the runtime-neutral image of a Dovetail `JustifiedSubterm` (op label
/// stringified). It is structurally a [`GroundTerm`]-shaped tree, so a runtime
/// bridge can rebuild it into a reflectable ground term without any Dovetail or
/// Rho dependency. `constructor` carries whatever op label the e-graph held (for
/// the generated report path a fully-qualified `"Lang::Cat::Ctor"`); a consumer
/// that reflects σ maps it to the bare constructor it needs.
///
/// [`GroundTerm`]: the Rho-codegen ground-term reflector input; this type mirrors
/// its `{ constructor, children }` shape without taking that dependency.
pub struct RuntimeReflectedSubterm {
    pub constructor: String,
    pub children: Vec<RuntimeReflectedSubterm>,
}

impl fmt::Debug for RuntimeReflectedSubterm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum DebugTask<'a> {
            Visit(&'a RuntimeReflectedSubterm),
            Separator,
            Tail,
        }

        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Visit(term) => {
                    write!(
                        formatter,
                        "RuntimeReflectedSubterm {{ constructor: {:?}, children: [",
                        term.constructor
                    )?;
                    tasks.push(DebugTask::Tail);
                    for (index, child) in term.children.iter().enumerate().rev() {
                        tasks.push(DebugTask::Visit(child));
                        if index > 0 {
                            tasks.push(DebugTask::Separator);
                        }
                    }
                },
                DebugTask::Separator => formatter.write_str(", ")?,
                DebugTask::Tail => formatter.write_str("] }")?,
            }
        }
        Ok(())
    }
}

impl PartialEq for RuntimeReflectedSubterm {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.constructor != right.constructor || left.children.len() != right.children.len()
            {
                return false;
            }
            pending.extend(left.children.iter().zip(&right.children));
        }
        true
    }
}

impl Eq for RuntimeReflectedSubterm {}

impl Clone for RuntimeReflectedSubterm {
    fn clone(&self) -> Self {
        enum CloneTask<'a> {
            Visit(&'a RuntimeReflectedSubterm),
            Assemble { constructor: String, child_count: usize },
        }

        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(term) => {
                    tasks.push(CloneTask::Assemble {
                        constructor: term.constructor.clone(),
                        child_count: term.children.len(),
                    });
                    for child in term.children.iter().rev() {
                        tasks.push(CloneTask::Visit(child));
                    }
                },
                CloneTask::Assemble { constructor, child_count } => {
                    let first_child = values
                        .len()
                        .checked_sub(child_count)
                        .expect("RuntimeReflectedSubterm clone PDA lost a child result");
                    let children = values.split_off(first_child);
                    values.push(Self { constructor, children });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("RuntimeReflectedSubterm clone PDA produced no result")
    }
}

impl Drop for RuntimeReflectedSubterm {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        pending.append(&mut self.children);
        while let Some(mut child) = pending.pop() {
            pending.append(&mut child.children);
        }
    }
}

impl RuntimeReflectedSubterm {
    /// Rewrite every constructor label in pre-order without using the host call stack.
    pub fn relabel_constructors(&mut self, mut relabel: impl FnMut(&str) -> String) {
        let mut pending = vec![self];
        while let Some(term) = pending.pop() {
            term.constructor = relabel(&term.constructor);
            for child in term.children.iter_mut().rev() {
                pending.push(child);
            }
        }
    }
}

/// One rewrite firing's justification projected into the runtime envelope: the
/// rule label plus the substitution σ that fired it, each σ variable mapped to
/// its funded-best extracted sub-term (ordered by variable name).
///
/// Empty [`rewrite_justifications`](RuntimeDovetailRunReport::rewrite_justifications)
/// in production `exec` reports (additive, byte-identical). A Rho runtime bridge
/// reads `sigma` to reflect the matched sub-terms into a σ-injection call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeRewriteJustification {
    pub rule_label: String,
    pub sigma: Vec<(String, RuntimeReflectedSubterm)>,
    /// The firing's **contractum** — the reduct `RHS[σ]` the host produced (incl.
    /// capture-avoiding substitution for a β-style substitution rewrite). A binder
    /// (Stage 3c) Rho σ-injection reads this: the host computes the substitution
    /// (model-b) and the reduced term reflects to the ground σ slot the flat
    /// σ-receiver fires. `None` when the report producer did not resolve it
    /// (additive; base/AC/contextual σ-injections ignore it and stay byte-identical).
    pub contractum: Option<RuntimeReflectedSubterm>,
}

/// Structural validation failure for a runtime-projected Dovetail report.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RuntimeDovetailReportError {
    RootOrdinalCountMismatch {
        roots: usize,
        root_ordinals: usize,
    },
    RootOrdinalOutOfBounds {
        root_index: usize,
        ordinal: usize,
        terms: usize,
    },
    RootKeyMismatch {
        root_index: usize,
        ordinal: usize,
    },
    RootTermNotMarked {
        root_index: usize,
        ordinal: usize,
    },
    TermOrdinalMismatch {
        index: usize,
        ordinal: usize,
    },
    DuplicateTermKey {
        ordinal: usize,
    },
    EdgeOrdinalMismatch {
        index: usize,
        ordinal: usize,
    },
    EdgeParentMissing {
        edge_ordinal: usize,
    },
    EdgeChildMissing {
        edge_ordinal: usize,
    },
    RuleFiringOrdinalMismatch {
        index: usize,
        ordinal: usize,
    },
    RuleFiringZeroCount {
        ordinal: usize,
    },
    RootFlagWithoutRootKey {
        ordinal: usize,
    },
}

impl fmt::Display for RuntimeDovetailReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeDovetailReportError::RootOrdinalCountMismatch { roots, root_ordinals } => {
                write!(
                    f,
                    "root count {roots} does not match root ordinal count {root_ordinals}"
                )
            },
            RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                root_index,
                ordinal,
                terms,
            } => write!(
                f,
                "root {root_index} points to term ordinal {ordinal}, but report has {terms} terms"
            ),
            RuntimeDovetailReportError::RootKeyMismatch { root_index, ordinal } => write!(
                f,
                "root {root_index} key does not match term ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::RootTermNotMarked { root_index, ordinal } => write!(
                f,
                "root {root_index} points to term ordinal {ordinal}, but that term is not marked as a root"
            ),
            RuntimeDovetailReportError::TermOrdinalMismatch { index, ordinal } => write!(
                f,
                "term at table index {index} records ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::DuplicateTermKey { ordinal } => {
                write!(f, "term ordinal {ordinal} duplicates an earlier exact key")
            },
            RuntimeDovetailReportError::EdgeOrdinalMismatch { index, ordinal } => write!(
                f,
                "derivation edge at table index {index} records ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::EdgeParentMissing { edge_ordinal } => write!(
                f,
                "derivation edge ordinal {edge_ordinal} references a missing parent term key"
            ),
            RuntimeDovetailReportError::EdgeChildMissing { edge_ordinal } => write!(
                f,
                "derivation edge ordinal {edge_ordinal} references a missing child term key"
            ),
            RuntimeDovetailReportError::RuleFiringOrdinalMismatch { index, ordinal } => write!(
                f,
                "rule firing at table index {index} records ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::RuleFiringZeroCount { ordinal } => write!(
                f,
                "rule firing ordinal {ordinal} records a zero merge count"
            ),
            RuntimeDovetailReportError::RootFlagWithoutRootKey { ordinal } => write!(
                f,
                "term ordinal {ordinal} is marked as a root but is absent from the report roots"
            ),
        }
    }
}

impl std::error::Error for RuntimeDovetailReportError {}

/// Runtime-neutral projection of `dovetail::report::DovetailRunReport`.
///
/// The generic runtime crate cannot depend on Dovetail without reversing the
/// intended dependency direction, so this type carries the report data in
/// runtime-owned terms: exact keys, deterministic ordinals, display strings,
/// ordered derivation edges, and explicit completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailRunReport {
    pub roots: Vec<ExactTermKey>,
    pub root_ordinals: Vec<usize>,
    pub terms: Vec<RuntimeDovetailTermRecord>,
    pub derivation_edges: Vec<RuntimeDovetailDerivationEdge>,
    pub rule_firings: Vec<RuntimeDovetailRuleFiring>,
    /// Per-firing σ justifications: each fired rewrite's label plus the matched
    /// sub-terms it fired under. Empty in production `exec` reports and every
    /// existing producer (additive, byte-identical — mirrors the
    /// [`source_display`](RuntimeDovetailTermRecord::source_display) None-default
    /// precedent). Populated only when a producer resolves σ provenance for a
    /// runtime bridge (Epic-4 Rho σ-injection).
    pub rewrite_justifications: Vec<RuntimeRewriteJustification>,
    /// ★ The declared fold bodies that DECLINED, and why.
    ///
    /// A fold that produced no value used to be indistinguishable from a rule that simply did not
    /// apply: both left the redex unreduced and both were reported as nothing at all, so a run
    /// over `6 / 0` came back as *"already a normal form"* over the term `6 / 0`. This field is
    /// the missing half — one record per distinct `(label, partiality)`, carrying a count and the
    /// reason (see [`crate::partiality`]).
    ///
    /// ⚠ **Semantic declines only.** A fold that did not fire because an operand is still a redex
    /// — a free variable, an unreduced child — is STRUCTURAL and is deliberately absent here;
    /// that is "not yet", and a later iteration may supply the answer. Without that exclusion
    /// every non-firing rule in the corpus would appear as a finding.
    ///
    /// Empty for every run in which nothing declined, and empty in every producer that does not
    /// run the Dovetail fold dispatcher (additive — it mirrors the
    /// [`rewrite_justifications`](Self::rewrite_justifications) empty-default precedent, and no
    /// computed value or post-state hash depends on it).
    pub declined_folds: Vec<crate::partiality::DeclinedFold>,
    pub completeness: RuntimeDovetailCompleteness,
    /// What the [`derivation_edges`](Self::derivation_edges) relation MEANS, so a consumer can
    /// project the right navigable graph. Production `exec` reports and the legacy step-display
    /// producer leave this [`Derivation`](RuntimeDovetailGraphKind::Derivation) (the default — the
    /// per-term derivation-dependency DAG, edges = child positions of a term's funded-best
    /// derivation). The REPL `step` rewrite-graph producer (`dovetail_step_graph`) sets it to
    /// [`Rewrite`](RuntimeDovetailGraphKind::Rewrite): each term is a WHOLE program state and each
    /// edge is a one-step rewrite successor (parent → child). The two shapes are projected
    /// differently in the REPL; the field is the unambiguous discriminator.
    pub graph_kind: RuntimeDovetailGraphKind,
}

/// What a [`RuntimeDovetailRunReport`]'s edge relation encodes — see
/// [`RuntimeDovetailRunReport::graph_kind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RuntimeDovetailGraphKind {
    /// Edges are derivation dependencies: `child_index` is a child position within a term's
    /// funded-best derivation tree, and `terms` are the e-classes that derivation references.
    /// This is the default and the only shape production `exec` ever produces.
    #[default]
    Derivation,
    /// Edges are one-step rewrite successors: `parent_key → child_key` means "the parent program
    /// state rewrites in one small step to the child state". `terms` are whole program states
    /// (each `source_display` rendered), `root_ordinals` is the single entry state, and a state
    /// with no outgoing edge is a normal form. Produced only by the step-only rewrite enumerator.
    Rewrite,
}

impl RuntimeDovetailRunReport {
    pub fn is_complete(&self) -> bool {
        self.completeness == RuntimeDovetailCompleteness::Complete
    }

    pub fn assert_complete(&self) -> Result<(), RuntimeDovetailCompleteness> {
        if self.is_complete() {
            Ok(())
        } else {
            Err(self.completeness)
        }
    }

    pub fn validate_shape(&self) -> Result<(), RuntimeDovetailReportError> {
        if self.roots.len() != self.root_ordinals.len() {
            return Err(RuntimeDovetailReportError::RootOrdinalCountMismatch {
                roots: self.roots.len(),
                root_ordinals: self.root_ordinals.len(),
            });
        }

        let mut term_keys = HashSet::with_capacity(self.terms.len());
        for (index, term) in self.terms.iter().enumerate() {
            if term.ordinal != index {
                return Err(RuntimeDovetailReportError::TermOrdinalMismatch {
                    index,
                    ordinal: term.ordinal,
                });
            }
            if !term_keys.insert(term.key.clone()) {
                return Err(RuntimeDovetailReportError::DuplicateTermKey { ordinal: term.ordinal });
            }
        }

        let mut root_keys = HashSet::with_capacity(self.roots.len());
        for (root_index, (root_key, ordinal)) in self
            .roots
            .iter()
            .zip(self.root_ordinals.iter().copied())
            .enumerate()
        {
            let term = self.terms.get(ordinal).ok_or(
                RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                    root_index,
                    ordinal,
                    terms: self.terms.len(),
                },
            )?;
            if term.key != *root_key {
                return Err(RuntimeDovetailReportError::RootKeyMismatch { root_index, ordinal });
            }
            if !term.is_root {
                return Err(RuntimeDovetailReportError::RootTermNotMarked { root_index, ordinal });
            }
            root_keys.insert(root_key.clone());
        }

        for term in &self.terms {
            if term.is_root && !root_keys.contains(&term.key) {
                return Err(RuntimeDovetailReportError::RootFlagWithoutRootKey {
                    ordinal: term.ordinal,
                });
            }
        }

        for (index, edge) in self.derivation_edges.iter().enumerate() {
            if edge.ordinal != index {
                return Err(RuntimeDovetailReportError::EdgeOrdinalMismatch {
                    index,
                    ordinal: edge.ordinal,
                });
            }
            if !term_keys.contains(&edge.parent_key) {
                return Err(RuntimeDovetailReportError::EdgeParentMissing {
                    edge_ordinal: edge.ordinal,
                });
            }
            if !term_keys.contains(&edge.child_key) {
                return Err(RuntimeDovetailReportError::EdgeChildMissing {
                    edge_ordinal: edge.ordinal,
                });
            }
        }

        for (index, firing) in self.rule_firings.iter().enumerate() {
            if firing.ordinal != index {
                return Err(RuntimeDovetailReportError::RuleFiringOrdinalMismatch {
                    index,
                    ordinal: firing.ordinal,
                });
            }
            if firing.count == 0 {
                return Err(RuntimeDovetailReportError::RuleFiringZeroCount {
                    ordinal: firing.ordinal,
                });
            }
        }

        Ok(())
    }

    pub fn term_by_key(&self, key: &[u8]) -> Option<&RuntimeDovetailTermRecord> {
        self.terms.iter().find(|term| term.key.as_slice() == key)
    }

    pub fn root_count(&self) -> usize {
        self.roots.len()
    }
}

/// The engine that produced a reduction step — drives the per-node label in the REPL's
/// linear-chain projection and the one-way Dovetail→Rho phase composition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeReductionEngine {
    /// A Rho-machine COMM rendezvous (produce/consume) on the cost-metered RSpace.
    RhoComm,
    /// A MeTTaIL native fold reduced in Dovetail — the pre-phase, or a Tier-3 runtime fold contract.
    DovetailFold,
    /// A stuck fold over a COMM-received value (Tier-2 detect-and-report): not reducible one-shot
    /// under the one-way bridge; surfaced, never silently mis-reduced.
    Stuck,
}

impl RuntimeReductionEngine {
    pub fn label(&self) -> &'static str {
        match self {
            RuntimeReductionEngine::RhoComm => "Rho COMM",
            RuntimeReductionEngine::DovetailFold => "Dovetail fold",
            RuntimeReductionEngine::Stuck => "stuck",
        }
    }
}

/// The kind of a single Rho-machine reduction within a `RhoComm`-engine step. The reactive stepper
/// observes every meaningful reduction, not just COMM rendezvous; `engine` stays `RhoComm` for all of
/// them and `kind` discriminates the COMM from the structural reductions (dereference, method,
/// `match`/`if`/`new`/`bundle` body). `Comm` is set directly when rendering a COMM event; the
/// structural kinds map 1:1 from the fork's `rspace_plus_plus::rspace::logging::ReductionKind`. (A
/// resting output is the *result* of the last reduction, not a separate reduction, so there is no
/// output kind.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeReductionKind {
    /// A COMM rendezvous (the structured `comm` payload is `Some`).
    Comm,
    /// Dereference `*N`.
    Deref,
    /// A `match` case body firing.
    Match,
    /// An `if` branch firing.
    If,
    /// A `new` scope body.
    New,
    /// A `bundle` body.
    Bundle,
    /// A method call re-eval.
    Method,
    /// A value resting on the observation channel at quiescence — the program's observable output.
    /// Read from the tuplespace post-`inj` and scoped to the configured channel, so (unlike a
    /// produce-time hook) it surfaces only the truly-resting output, never a consumed internal send.
    Output,
}

impl RuntimeReductionKind {
    pub fn label(&self) -> &'static str {
        match self {
            RuntimeReductionKind::Comm => "COMM",
            RuntimeReductionKind::Deref => "deref",
            RuntimeReductionKind::Match => "match",
            RuntimeReductionKind::If => "if",
            RuntimeReductionKind::New => "new",
            RuntimeReductionKind::Bundle => "bundle",
            RuntimeReductionKind::Method => "method",
            RuntimeReductionKind::Output => "output",
        }
    }
}

/// A committed COMM event observed on the Rho machine (the reactive single-stepper emit payload).
#[derive(Debug, Clone)]
pub struct RuntimeCommEvent {
    /// The rendezvous channel(s), rendered.
    pub channels: Vec<String>,
    /// The data matched/consumed by the rendezvous, rendered.
    pub consumed: Vec<String>,
    /// `"comm.consume"` or `"comm.produce"` — which side observed the COMM.
    pub label: String,
    /// The firing receive's continuation body (e.g. `*x`), rendered — the receive side of the
    /// rendezvous, surfaced so both the send and the receive are visible. `None` when the
    /// continuation is not a `ParBody`.
    pub continuation: Option<String>,
}

/// A-S5.6 (F5, τ-COMM UX): the internal-machinery class of one live-trace COMM, decided
/// by the channel classifier over the DETERMINISTIC reserved channel names (the
/// `^…:{fp}` observation GStrings + the reconstructible GPrivate reflect tags). A
/// classified COMM is a τ step — reduction MACHINERY (driver dispatch, subst-TRS
/// computation, AC-carrier plumbing), not a surface-visible firing — and the REPL
/// step display filters τ steps out by default (`:taus` / `step --taus` shows all;
/// USER-overridable Q-τ default).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeTauClass {
    /// The `^drive` quiescence-driver family: the driver rendezvous tag plus the
    /// `^fired`/`^drive-err`/`^drive-fuel` observation channels.
    Drive,
    /// The `^subst` de-Bruijn TRS family (`^subst`/`^shift`/`^shiftk`/`^cmp`/`^pred`/
    /// `^sb`/`^shb`).
    Subst,
    /// The per-rule AC carrier family (`^drive-ac:{RuleLabel}`).
    Ac,
    /// A-S5.8 (F8-AM-2): the `^float` binder-float canonicalizer family — the `^float`
    /// dispatcher rendezvous plus the per-constructor / per-op satellites
    /// (`^float-hoist:{C}` / `^float-merge:{op}`). Float COMMs are `≡`-canonicalization
    /// machinery (cost-free iso in KT terms — never in the firing ledger, never drive
    /// fuel), filtered like every τ family. The shared `^shift`/`^cmp` satellites the
    /// float calls stay `[τ subst]` (families disjoint — no existing label
    /// reclassifies).
    Float,
}

impl RuntimeTauClass {
    /// The REPL display label (`[τ drive]` / `[τ subst]` / `[τ ac]` / `[τ float]`).
    pub fn label(&self) -> &'static str {
        match self {
            RuntimeTauClass::Drive => "τ drive",
            RuntimeTauClass::Subst => "τ subst",
            RuntimeTauClass::Ac => "τ ac",
            RuntimeTauClass::Float => "τ float",
        }
    }
}

/// One reduction step in a live Rho-machine COMM trace (the reactive single-stepper).
#[derive(Debug, Clone)]
pub struct RuntimeReductionStep {
    /// 0-based deterministic emit ordinal — also the node id in the REPL linear chain.
    pub ordinal: u64,
    /// Which engine produced this step (always `RhoComm` for the live Rho-machine reduction trace).
    pub engine: RuntimeReductionEngine,
    /// The kind of reduction — COMM vs the structural deref/match/if/new/bundle/method/output.
    pub kind: RuntimeReductionKind,
    /// A one-line rendering of the step (the COMM event, the deref/output redex, etc.).
    pub display: String,
    /// The structured COMM payload when `kind == Comm`.
    pub comm: Option<RuntimeCommEvent>,
    /// A-S5.6: `Some` iff this COMM fired on a reserved internal-machinery channel
    /// (see [`RuntimeTauClass`]); `None` for surface-visible COMMs and outputs.
    pub tau: Option<RuntimeTauClass>,
}

/// An ordered live single-step reduction trace from the Rho machine. Each entry is one COMM (the
/// principled process-calculus reduction unit), with Dovetail fold steps interleaved only when a
/// Tier-3 runtime fold contract fires. Projected by the REPL into a navigable linear chain.
#[derive(Debug, Clone, Default)]
pub struct RuntimeReductionTrace {
    pub steps: Vec<RuntimeReductionStep>,
}

impl RuntimeReductionTrace {
    pub fn new(steps: Vec<RuntimeReductionStep>) -> Self {
        Self { steps }
    }

    pub fn step_count(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// A live, incremental Rho-machine COMM single-stepper (the reactive stepper), returned by
/// [`Language::start_reduction_stepper`] and held by the REPL across advance commands. Each
/// `next_step` advances the reduction by exactly one COMM (pay-as-you-go — works for divergent
/// Rholang, halt anytime). Dropping the stepper aborts the underlying worker (the back-pressure
/// gate is closed and the worker thread joined). `Send` so the REPL can store it in its state.
pub trait ReductionStepper: Send {
    /// Advance the reduction by one COMM and return that step, or `None` once the reduction has
    /// reached quiescence (no further COMMs fire). `Err(msg)` on an interpreter or abort error.
    fn next_step(&mut self) -> Result<Option<RuntimeReductionStep>, String>;
}

/// Runtime-neutral output of an installed backend.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum RuntimeBackendOutput {
    /// Legacy/reference rewrite graph materialized as Ascent facts.
    Ascent(AscentResults),
    /// Checked Dovetail extraction report.
    Dovetail(RuntimeDovetailRunReport),
    /// Resting observations from a substrate such as RSpace.
    Observations(Vec<RuntimeChannelObservation>),
    /// Ordered live single-step COMM reduction trace from the Rho machine (reactive stepper).
    ReductionTrace(RuntimeReductionTrace),
}

impl RuntimeBackendOutput {
    pub fn kind_name(&self) -> &'static str {
        match self {
            RuntimeBackendOutput::Ascent(_) => "AscentResults",
            RuntimeBackendOutput::Dovetail(_) => "DovetailRunReport",
            RuntimeBackendOutput::Observations(_) => "runtime observations",
            RuntimeBackendOutput::ReductionTrace(_) => "reduction trace",
        }
    }
}

/// Runtime-neutral report returned by a selected backend.
#[derive(Debug, Clone)]
pub struct RuntimeBackendReport {
    backend: RuntimeBackend,
    artifact: RuntimeBackendArtifact,
    output: RuntimeBackendOutput,
}

impl RuntimeBackendReport {
    pub fn ascent(results: AscentResults) -> Self {
        Self {
            backend: RuntimeBackend::Ascent,
            artifact: RuntimeBackendArtifact::AscentFixpoint,
            output: RuntimeBackendOutput::Ascent(results),
        }
    }

    pub fn try_observations(
        backend: RuntimeBackend,
        artifact: RuntimeBackendArtifact,
        observations: Vec<RuntimeChannelObservation>,
    ) -> Result<Self, RuntimeObservationReportError> {
        if backend != RuntimeBackend::RhoMachine {
            return Err(RuntimeObservationReportError::InvalidObservationBackend { backend });
        }
        match artifact {
            RuntimeBackendArtifact::RhoNormalizedAst | RuntimeBackendArtifact::RhoBytecode => {},
            artifact => {
                return Err(RuntimeObservationReportError::InvalidObservationArtifact {
                    backend,
                    artifact,
                });
            },
        }
        Ok(Self {
            backend,
            artifact,
            output: RuntimeBackendOutput::Observations(observations),
        })
    }

    pub fn try_dovetail(
        report: RuntimeDovetailRunReport,
    ) -> Result<Self, RuntimeDovetailReportError> {
        report.validate_shape()?;
        Ok(Self {
            backend: RuntimeBackend::Dovetail,
            artifact: RuntimeBackendArtifact::DovetailRunReport,
            output: RuntimeBackendOutput::Dovetail(report),
        })
    }

    pub fn backend(&self) -> RuntimeBackend {
        self.backend
    }

    pub fn artifact(&self) -> RuntimeBackendArtifact {
        self.artifact
    }

    pub fn output(&self) -> &RuntimeBackendOutput {
        &self.output
    }

    pub fn into_output(self) -> RuntimeBackendOutput {
        self.output
    }

    /// Construct a Rho-machine reduction-trace report (the reactive single-stepper output). Always
    /// `RhoMachine` / `RhoNormalizedAst` — the trace is inherently a live Rho-machine artifact, so
    /// no backend/artifact validation branch is needed.
    pub fn reduction_trace(trace: RuntimeReductionTrace) -> Self {
        Self {
            backend: RuntimeBackend::RhoMachine,
            artifact: RuntimeBackendArtifact::RhoNormalizedAst,
            output: RuntimeBackendOutput::ReductionTrace(trace),
        }
    }

    pub fn as_ascent_results(&self) -> Option<&AscentResults> {
        match &self.output {
            RuntimeBackendOutput::Ascent(results) => Some(results),
            RuntimeBackendOutput::Dovetail(_) => None,
            RuntimeBackendOutput::Observations(_) => None,
            RuntimeBackendOutput::ReductionTrace(_) => None,
        }
    }

    pub fn into_ascent_results(self) -> Result<AscentResults, Self> {
        match self.output {
            RuntimeBackendOutput::Ascent(results) => Ok(results),
            RuntimeBackendOutput::Dovetail(_) => Err(self),
            RuntimeBackendOutput::Observations(_) => Err(self),
            RuntimeBackendOutput::ReductionTrace(_) => Err(self),
        }
    }

    pub fn as_reduction_trace(&self) -> Option<&RuntimeReductionTrace> {
        match &self.output {
            RuntimeBackendOutput::ReductionTrace(trace) => Some(trace),
            RuntimeBackendOutput::Ascent(_) => None,
            RuntimeBackendOutput::Dovetail(_) => None,
            RuntimeBackendOutput::Observations(_) => None,
        }
    }

    pub fn as_dovetail(&self) -> Option<&RuntimeDovetailRunReport> {
        match &self.output {
            RuntimeBackendOutput::Dovetail(report) => Some(report),
            RuntimeBackendOutput::Ascent(_) => None,
            RuntimeBackendOutput::Observations(_) => None,
            RuntimeBackendOutput::ReductionTrace(_) => None,
        }
    }

    pub fn observations_for_channel(&self, channel: &str) -> Option<&RuntimeChannelObservation> {
        match &self.output {
            RuntimeBackendOutput::Ascent(_) => None,
            RuntimeBackendOutput::Dovetail(_) => None,
            RuntimeBackendOutput::Observations(observations) => observations
                .iter()
                .find(|observation| observation.channel == channel),
            RuntimeBackendOutput::ReductionTrace(_) => None,
        }
    }
}

/// Exact rewrite-graph seed.
///
/// `term_id` remains for compatibility and diagnostics. `exact_key`, when
/// present, is the no-loss reachability key used by normal-form traversal.
#[derive(Debug, Clone, PartialEq)]
pub struct RewriteSeed {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
}

impl RewriteSeed {
    pub fn legacy(term_id: u64, display: String) -> Self {
        Self { term_id, exact_key: None, display }
    }

    pub fn exact(term_id: u64, exact_key: ExactTermKey, display: String) -> Self {
        Self {
            term_id,
            exact_key: Some(exact_key),
            display,
        }
    }
}

/// Exact weighted rewrite-graph seed.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightedRewriteSeed {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
    pub weight: f64,
}

impl WeightedRewriteSeed {
    pub fn legacy(term_id: u64, display: String, weight: f64) -> Self {
        Self {
            term_id,
            exact_key: None,
            display,
            weight,
        }
    }

    pub fn exact(term_id: u64, exact_key: ExactTermKey, display: String, weight: f64) -> Self {
        Self {
            term_id,
            exact_key: Some(exact_key),
            display,
            weight,
        }
    }
}

// =============================================================================
// Type Inference Types
// =============================================================================

/// Runtime representation of inferred types for REPL display
///
/// This mirrors the compile-time `InferredType` but is available at runtime
/// for displaying types to users.
pub enum TermType {
    /// Base type: Name, Proc, etc.
    Base(String),
    /// Function type: [Domain -> Codomain]
    Arrow(Box<TermType>, Box<TermType>),
    /// Multi-argument function type: [Domain* -> Codomain]
    MultiArrow(Box<TermType>, Box<TermType>),
    /// Phase D.7 (2026-05-17, M14.4): union type capturing inference
    /// over an `Ambiguous(Vec<Inner>)` term. Each alternative's
    /// inferred type lives in the inner vec; downstream callers can
    /// inspect every typing or pick one.
    ///
    /// Constructor `union(types)` deduplicates and collapses
    /// trivial cases: empty → `Unknown`; single-elem → that element;
    /// otherwise the resulting `Ambiguous(Vec<TermType>)`.
    Ambiguous(Vec<TermType>),
    /// Unknown type (inference failed or not applicable)
    Unknown,
}

mod term_type_lifecycle;

impl TermType {
    /// Create a base type
    pub fn base(name: impl Into<String>) -> Self {
        TermType::Base(name.into())
    }

    /// Create a function type
    pub fn arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::Arrow(Box::new(domain), Box::new(codomain))
    }

    /// Create a multi-argument function type
    pub fn multi_arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::MultiArrow(Box::new(domain), Box::new(codomain))
    }

    /// Phase D.7 (2026-05-17, M14.4): construct an `Ambiguous` union
    /// type with trivial-case folding. Pass in any number of
    /// alternatives; the constructor deduplicates them and collapses:
    ///   - empty input  → `Unknown`
    ///   - 1 unique     → the single element (no wrapper)
    ///   - 2+ unique    → `Ambiguous(Vec<TermType>)`
    pub fn union(types: Vec<TermType>) -> Self {
        // Flatten nested Ambiguous and deduplicate.
        let mut seen: Vec<TermType> = Vec::with_capacity(types.len());
        for ty in types {
            let to_add = term_type_lifecycle::into_ambiguous(ty);
            for t in to_add {
                if !seen.contains(&t) {
                    seen.push(t);
                }
            }
        }
        match seen.len() {
            0 => TermType::Unknown,
            1 => seen.into_iter().next().expect("checked len == 1"),
            _ => TermType::Ambiguous(seen),
        }
    }

    /// Check if this is a function type
    pub fn is_function(&self) -> bool {
        matches!(self, TermType::Arrow(..) | TermType::MultiArrow(..))
    }

    /// Get the domain type if this is a function type
    pub fn domain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(d, _) | TermType::MultiArrow(d, _) => Some(d),
            _ => None,
        }
    }

    /// Get the codomain type if this is a function type
    pub fn codomain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(_, c) | TermType::MultiArrow(_, c) => Some(c),
            _ => None,
        }
    }
}

/// Information about a variable's type in a term
#[derive(Debug, Clone)]
pub struct VarTypeInfo {
    /// The variable name
    pub name: String,
    /// The inferred type
    pub ty: TermType,
}

impl fmt::Display for VarTypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {}", self.name, self.ty)
    }
}

/// A trait for terms (AST nodes) that can be manipulated generically
pub trait Term: fmt::Display + fmt::Debug + Send + Sync {
    /// Clone this term into a Box
    fn clone_box(&self) -> Box<dyn Term>;

    /// Get a unique identifier for this term (for equality comparison)
    fn term_id(&self) -> u64;

    /// Check if this term is equal to another
    fn term_eq(&self, other: &dyn Term) -> bool;

    /// Get this as Any for downcasting
    fn as_any(&self) -> &dyn Any;

    /// Phase F.12.A (2026-05-20): return the rewrite-graph seeds for each
    /// single-category derivation this term represents.
    ///
    /// For unambiguous terms this returns exactly one entry whose `term_id`
    /// equals `self.term_id()`. For `Ambiguous` wrappers, each inner alt
    /// contributes one entry whose exact key, when present, MUST match the
    /// corresponding `TermInfo.exact_key` in `run_ascent`.
    ///
    /// Default impl: returns a legacy `term_id` seed,
    /// which is correct for any language that has no `Ambiguous` variant.
    /// Generated `impl Term for <Lang>Term` blocks override this when the
    /// language has cross-category projection.
    fn rewrite_seeds(&self) -> Vec<RewriteSeed> {
        vec![RewriteSeed::legacy(self.term_id(), format!("{}", self))]
    }

    /// Compatibility surface for callers that still carry only a 64-bit graph
    /// id. New code should prefer `rewrite_seeds` so the exact key survives
    /// into reachability traversal.
    fn rewrite_seed_ids(&self) -> Vec<(u64, String)> {
        self.rewrite_seeds()
            .into_iter()
            .map(|seed| (seed.term_id, seed.display))
            .collect()
    }

    /// Weighted variant of `rewrite_seeds`.
    fn rewrite_weighted_seeds(&self) -> Vec<WeightedRewriteSeed> {
        self.rewrite_seeds()
            .into_iter()
            .map(|seed| WeightedRewriteSeed {
                term_id: seed.term_id,
                exact_key: seed.exact_key,
                display: seed.display,
                weight: 0.0,
            })
            .collect()
    }

    /// Weighted variant of `rewrite_seed_ids`.
    ///
    /// Terms do not generally store parse/evidence weights, so the default
    /// exposes neutral weight. Parser surfaces that still have access to
    /// derivation weights should return their own weighted seed list.
    fn rewrite_weighted_seed_ids(&self) -> Vec<WeightedSeedId> {
        self.rewrite_weighted_seeds()
            .into_iter()
            .map(|seed| (seed.term_id, seed.display, seed.weight))
            .collect()
    }
}

/// A trait that all languages must implement
///
/// This trait is auto-generated by the `language!` macro.
pub trait Language: Send + Sync {
    /// Get the name of this language (e.g., "Rholang")
    fn name(&self) -> &'static str;

    /// Get static metadata for this language (types, terms, equations, rewrites)
    fn metadata(&self) -> &'static dyn LanguageMetadata;

    /// Parse a term from a string (clears var cache for fresh evaluation)
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Parse a term for environment storage (does NOT clear var cache)
    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Parse a term and return weighted rewrite seeds for lazy evaluation.
    ///
    /// The default falls back to neutral weights for languages whose generated
    /// parser does not expose derivation weights. Multi-category generated
    /// languages override this to preserve WPDA parse/evidence weights.
    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        let (term, seeds) = self.parse_term_with_weighted_rewrite_seeds(input)?;
        Ok((
            term,
            seeds
                .into_iter()
                .map(|seed| (seed.term_id, seed.display, seed.weight))
                .collect(),
        ))
    }

    /// Parse a term and return exact weighted rewrite seeds for lazy
    /// evaluation. Generated languages override this to preserve parse/evidence
    /// weights and exact semantic keys. Legacy implementations inherit exact
    /// absence and neutral weights from `Term::rewrite_weighted_seeds`.
    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        let term = self.parse_term(input)?;
        let seeds = term.rewrite_weighted_seeds();
        Ok((term, seeds))
    }

    /// Run the explicit Ascent reference oracle on a term and return results.
    ///
    /// Production runtime execution uses [`Language::run_backend_report`] and
    /// [`Language::run_default_backend_report`]. The default oracle hook fails
    /// closed so parse-only, Dovetail-backed, and Rho-backed language values do
    /// not have to provide an Ascent implementation merely to satisfy the
    /// trait. Generated or test languages that intentionally expose reference
    /// evidence override this method explicitly.
    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
        let _ = term;
        Err(format!(
            "Ascent oracle for language {} is not installed; use a generated oracle feature or an explicit reference wrapper",
            self.name()
        ))
    }

    /// Backend used by user-facing evaluation when no backend is requested
    /// explicitly.
    ///
    /// The runtime capability view must advertise only executable backends.
    /// When multiple entries are marked default, the first declaration wins,
    /// preserving the language author's generated order among production
    /// backends unless a wrapper deliberately installs a new default. Ascent is
    /// reference/oracle-only and is never selected as a production default.
    fn selected_default_runtime_backend(&self) -> Option<RuntimeBackend> {
        self.runtime_backend_capabilities()
            .iter()
            .find(|capability| {
                capability.is_default && capability.backend != RuntimeBackend::Ascent
            })
            .map(|capability| capability.backend)
    }

    /// Display/query view of the default backend.
    ///
    /// Runtime execution uses [`Language::selected_default_runtime_backend`]
    /// and fails closed when no default was explicitly advertised. This method
    /// mirrors that absence for metadata-only callers; it must not fabricate an
    /// Ascent default for a concrete language value that advertises no selected
    /// runtime backend.
    fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
        self.selected_default_runtime_backend()
    }

    /// Runtime backends executable for this concrete language value.
    ///
    /// The default derives from static generated metadata. Runtime wrappers may
    /// override this to expose plan-specific evidence, for example a
    /// flip-gated Rho backend installed around an otherwise substrate-neutral
    /// generated language.
    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        self.metadata()
            .runtime_backends()
            .iter()
            .map(RuntimeBackendCapability::from_static)
            .collect()
    }

    /// Whether this language currently exposes the selected backend through the
    /// generic runtime trait.
    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        self.runtime_backend_capabilities()
            .iter()
            .any(|capability| capability.backend == backend)
    }

    /// Run the selected backend and return a runtime-neutral report.
    ///
    /// This is the production backend surface for Dovetail/Rho integration.
    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Ascent => Err(format!(
                "Ascent report execution for language {} is oracle-only; use the explicit reference helper instead of the production runtime dispatcher",
                self.name()
            )),
            other => {
                let _ = term;
                Err(format!("{} backend is not installed for language {}", other, self.name()))
            },
        }
    }

    /// Run the language's selected default backend and return a runtime-neutral
    /// report.
    fn run_default_backend_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        let backend = self.selected_default_runtime_backend().ok_or_else(|| {
            format!("language {} does not advertise a default runtime backend", self.name())
        })?;
        self.run_backend_report(backend, term)
    }

    /// Run a **step-mode** backend report — the comprehensible, source-rendered counterpart of
    /// [`run_backend_report`](Self::run_backend_report)`(Dovetail, …)` for the REPL `step` command.
    ///
    /// The default delegates to the plain Dovetail report (op-name display, no source
    /// reconstruction), so a language without a step-aware backend is unchanged. The Dovetail+Rho
    /// wrapper overrides this to run the generated `dovetail_step_report`, whose term records carry
    /// `source_display` (reconstructed source syntax). This surface is reached **only** from the
    /// REPL's `step` routing — never from production `exec` — so it costs `exec` nothing.
    fn run_step_backend_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        self.run_backend_report(RuntimeBackend::Dovetail, term)
    }

    /// Start a **live, incremental** Rho-machine COMM single-stepper (the reactive stepper). The
    /// returned [`ReductionStepper`] advances by exactly one COMM per `next_step` (pay-as-you-go —
    /// works for divergent Rholang; halt anytime by dropping it). Default: fail closed — only the
    /// two-stage Dovetail+Rholang wrappers, which own a real f1r3node runtime, install this. The
    /// wrapper backs the stepper with a dedicated worker thread running `inj` with the COMM
    /// observer + back-pressure gate installed; dropping the box aborts the worker.
    fn start_reduction_stepper(
        &self,
        term: &dyn Term,
    ) -> Result<Box<dyn ReductionStepper>, String> {
        let _ = term;
        Err(format!(
            "language {} does not support live single-step COMM reduction tracing (no Rho-machine \
             stepper installed)",
            self.name()
        ))
    }

    /// Drive [`start_reduction_stepper`] to quiescence (or the safety cap) and return the whole
    /// ordered trace as a report — the non-interactive / test-facing surface (the REPL drives the
    /// stepper live instead). Capped so a divergent term cannot hang this convenience driver; the
    /// cap is far beyond any terminating Rho program the bundled languages produce.
    fn run_reduction_trace_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        const SAFETY_CAP: usize = 100_000;
        let mut stepper = self.start_reduction_stepper(term)?;
        let mut steps = Vec::new();
        while steps.len() < SAFETY_CAP {
            match stepper.next_step()? {
                Some(step) => steps.push(step),
                None => break,
            }
        }
        Ok(RuntimeBackendReport::reduction_trace(RuntimeReductionTrace::new(steps)))
    }

    /// Run Ascent on a term with pre-seeded relation facts.
    ///
    /// The `facts` map keys are relation names (e.g., `"certified"`)
    /// and values are tuples as string vectors (e.g.,
    /// `vec![vec!["item_A"]]`). Before fixpoint evaluation, the
    /// codegen:
    /// 1. Parses each tuple's strings into the relation's parameter
    ///    types and pushes them into the Ascent program struct
    /// 2. Populates the thread-local fact snapshot so the Comm rule's
    ///    `if { evaluate_pred_with_bindings(...) }` guard can check
    ///    per-instance predicates
    ///
    /// Default: delegates to `run_ascent` (ignores facts), which fails closed
    /// unless an explicit Ascent oracle implementation is installed.
    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = facts;
        self.run_ascent(term)
    }

    /// Run the selected backend with pre-seeded relation facts and return a
    /// runtime-neutral report.
    fn run_backend_report_with_facts(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Ascent => Err(format!(
                "seeded Ascent report execution for language {} is oracle-only; use the explicit reference helper instead of the production runtime dispatcher",
                self.name()
            )),
            other => {
                let _ = (term, facts);
                Err(format!(
                    "{} backend with seeded facts is not installed for language {}",
                    other,
                    self.name()
                ))
            },
        }
    }

    /// Run the language's selected default backend with pre-seeded relation
    /// facts and return a runtime-neutral report.
    fn run_default_backend_report_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        let backend = self.selected_default_runtime_backend().ok_or_else(|| {
            format!("language {} does not advertise a default runtime backend", self.name())
        })?;
        self.run_backend_report_with_facts(backend, term, facts)
    }

    /// If the term is fully evaluable (no free variables), evaluate it and return the result term.
    /// Otherwise return `None` (e.g. term contains vars, or language has no native eval).
    /// Default: `None` so languages without native types need not implement.
    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        let _ = term;
        None
    }

    /// Normalize a term (beta-reduce Apply/MApply of Lam/MLam, flatten collections, etc.)
    /// Default: returns a clone (no normalization).
    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        term.clone_box()
    }

    /// Format a term as a string
    fn format_term(&self, term: &dyn Term) -> String {
        format!("{}", term)
    }

    // === Environment Support ===

    /// Create a new empty environment for this language
    fn create_env(&self) -> Box<dyn Any + Send + Sync>;

    /// Add a term to the environment under the given name
    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String>;

    /// Remove a binding from the environment
    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String>;

    /// Clear all bindings from the environment
    fn clear_env(&self, env: &mut dyn Any);

    /// Apply environment substitution to a term (includes normalization/constant folding).
    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String>;

    /// Substitute environment variables without normalizing (no constant folding).
    /// Use for step mode so the term tree is preserved and rewrites can be applied one by one.
    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.substitute_env(term, env)
    }

    /// List all environment bindings as (name, display, optional_comment) tuples
    ///
    /// Returns bindings in insertion order, with any associated comments.
    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)>;

    /// Set a comment for a binding in the environment
    fn set_env_comment(&self, env: &mut dyn Any, name: &str, comment: String)
        -> Result<(), String>;

    /// Check if the environment is empty
    fn is_env_empty(&self, env: &dyn Any) -> bool;

    /// Get a term by name from the environment (any category).
    /// Used so that `exec z` uses the stored term for "z" instead of parsing "z" as a variable,
    /// which can leave e.g. IVar(z) unsubstituted when "z" is bound in another category (e.g. Proc).
    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        let _ = (env, name);
        None
    }

    // === Type Inference Support ===

    /// Infer the type of a term
    ///
    /// For lambda expressions, returns the full function type (e.g., `[Name -> Proc]`).
    /// For other terms, returns their category (e.g., `Proc`, `Name`).
    fn infer_term_type(&self, term: &dyn Term) -> TermType;

    /// Get all free variables and their inferred types in a term
    ///
    /// Returns a list of variable names with their types, inferred from
    /// how they are used in the term.
    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo>;

    /// Infer the type of a specific variable from its usage in a term
    ///
    /// Returns `None` if the variable is not found or its type cannot be inferred.
    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType>;
}

/// Results from running Ascent
#[derive(Debug, Clone)]
pub struct AscentResults {
    /// All reachable terms
    pub all_terms: Vec<TermInfo>,

    /// All rewrites (from -> to)
    pub rewrites: Vec<Rewrite>,

    /// Equivalence classes (terms related by equations)
    pub equivalences: Vec<EquivClass>,

    /// Custom relations: name -> relation data
    pub custom_relations: std::collections::HashMap<String, RelationData>,
}

/// Data for a custom relation
#[derive(Debug, Clone)]
pub struct RelationData {
    /// Parameter type names (e.g., ["Proc", "Proc"])
    pub param_types: Vec<String>,
    /// Tuples as formatted strings (each tuple is a Vec of formatted elements)
    pub tuples: Vec<Vec<String>>,
}

/// Information about a term in the rewrite graph
#[derive(Debug, Clone)]
pub struct TermInfo {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
    pub is_normal_form: bool,
}

/// A rewrite from one term to another
#[derive(Debug, Clone)]
pub struct Rewrite {
    pub from_id: u64,
    pub to_id: u64,
    pub from_key: Option<ExactTermKey>,
    pub to_key: Option<ExactTermKey>,
    pub rule_name: Option<String>,
}

/// An equivalence class of terms
#[derive(Debug, Clone)]
pub struct EquivClass {
    pub term_ids: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ReachKey {
    Exact(ExactTermKey),
    Legacy(u64),
}

impl TermInfo {
    fn reach_key(&self) -> ReachKey {
        self.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.term_id))
    }
}

impl Rewrite {
    fn from_reach_key(&self) -> ReachKey {
        self.from_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.from_id))
    }

    fn to_reach_key(&self) -> ReachKey {
        self.to_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.to_id))
    }
}

/// Lazy breadth-first iterator over normal forms reachable from one or more
/// rewrite-graph seeds.
///
/// The iterator preserves seed order and yields every reachable normal form by
/// graph identity. It does not rank by display text or any other presentation
/// heuristic. The rewrite adjacency index is built only when expansion is
/// needed, so an already-normal seed can be observed without scanning the whole
/// rewrite relation.
pub struct ReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: VecDeque<ReachKey>,
    visited: HashSet<ReachKey>,
    term_index: Option<HashMap<ReachKey, usize>>,
    rewrites_by_from: Option<HashMap<ReachKey, Vec<ReachKey>>>,
}

impl<'a> ReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, seed_ids: &[u64]) -> Self {
        let seeds: Vec<RewriteSeed> = seed_ids
            .iter()
            .flat_map(|&id| results.rewrite_seeds_for_legacy_id(id))
            .collect();
        Self::new_exact(results, &seeds)
    }

    fn new_exact(results: &'a AscentResults, seeds: &[RewriteSeed]) -> Self {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        for seed in seeds {
            let key = results.seed_reach_key(seed);
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
        Self {
            results,
            queue,
            visited,
            term_index: None,
            rewrites_by_from: None,
        }
    }

    fn term_info(&self, key: &ReachKey) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(key).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.term_info_by_reach_key(key)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.reach_key(), idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<ReachKey, Vec<ReachKey>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_reach_key())
                    .or_default()
                    .push(rewrite.to_reach_key());
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for ReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(key) = self.queue.pop_front() {
            let info = match self.term_info(&key) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&key))
                .cloned()
                .unwrap_or_default();
            for to_key in next_ids {
                if self.visited.insert(to_key.clone()) {
                    self.queue.push_back(to_key);
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy)]
struct WeightedQueueEntry {
    key_index: usize,
    weight: f64,
    sequence: usize,
}

impl PartialEq for WeightedQueueEntry {
    fn eq(&self, other: &Self) -> bool {
        self.key_index == other.key_index
            && self.weight.total_cmp(&other.weight) == Ordering::Equal
            && self.sequence == other.sequence
    }
}

impl Eq for WeightedQueueEntry {}

impl PartialOrd for WeightedQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for WeightedQueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // BinaryHeap pops the greatest element, so reverse the natural order:
        // lower weight first, then lower insertion sequence.
        other
            .weight
            .total_cmp(&self.weight)
            .then_with(|| other.sequence.cmp(&self.sequence))
            .then_with(|| other.key_index.cmp(&self.key_index))
    }
}

/// Lazy priority traversal over normal forms reachable from weighted seeds.
///
/// The queue orders work by the caller-provided seed weight, with seed order as
/// the deterministic tie breaker. Expansion indexes are still built only when a
/// non-normal term is popped, so an already-normal best seed can satisfy a
/// bounded prefix request without scanning the rewrite relation.
pub struct WeightedReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: BinaryHeap<WeightedQueueEntry>,
    keys: Vec<ReachKey>,
    key_index: HashMap<ReachKey, usize>,
    visited: HashSet<ReachKey>,
    term_index: Option<HashMap<ReachKey, usize>>,
    rewrites_by_from: Option<HashMap<ReachKey, Vec<ReachKey>>>,
    next_sequence: usize,
}

impl<'a> WeightedReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, weighted_seed_ids: &[(u64, f64)]) -> Self {
        let seeds: Vec<WeightedRewriteSeed> = weighted_seed_ids
            .iter()
            .flat_map(|&(id, weight)| {
                results
                    .rewrite_seeds_for_legacy_id(id)
                    .into_iter()
                    .map(move |seed| WeightedRewriteSeed {
                        term_id: seed.term_id,
                        exact_key: seed.exact_key,
                        display: seed.display,
                        weight,
                    })
            })
            .collect();
        Self::new_exact(results, &seeds)
    }

    fn new_exact(results: &'a AscentResults, weighted_seeds: &[WeightedRewriteSeed]) -> Self {
        let mut best_by_key: HashMap<ReachKey, (f64, usize)> = HashMap::new();
        for (sequence, seed) in weighted_seeds.iter().enumerate() {
            let weight = seed.weight;
            let weight = if weight.is_nan() {
                f64::INFINITY
            } else {
                weight
            };
            best_by_key
                .entry(results.weighted_seed_reach_key(seed))
                .and_modify(|best| {
                    if weight.total_cmp(&best.0) == Ordering::Less
                        || (weight.total_cmp(&best.0) == Ordering::Equal && sequence < best.1)
                    {
                        *best = (weight, sequence);
                    }
                })
                .or_insert((weight, sequence));
        }

        let mut queue = BinaryHeap::new();
        let mut keys = Vec::with_capacity(best_by_key.len());
        let mut key_index = HashMap::with_capacity(best_by_key.len());
        let mut visited = HashSet::new();
        let mut next_sequence = weighted_seeds.len();
        for (key, (weight, sequence)) in best_by_key {
            let idx = keys.len();
            key_index.insert(key.clone(), idx);
            keys.push(key.clone());
            visited.insert(key);
            next_sequence = next_sequence.max(sequence.saturating_add(1));
            queue.push(WeightedQueueEntry { key_index: idx, weight, sequence });
        }

        Self {
            results,
            queue,
            keys,
            key_index,
            visited,
            term_index: None,
            rewrites_by_from: None,
            next_sequence,
        }
    }

    fn key_index_for(&mut self, key: ReachKey) -> usize {
        if let Some(&idx) = self.key_index.get(&key) {
            return idx;
        }
        let idx = self.keys.len();
        self.keys.push(key.clone());
        self.key_index.insert(key, idx);
        idx
    }

    fn term_info(&self, key: &ReachKey) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(key).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.term_info_by_reach_key(key)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.reach_key(), idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<ReachKey, Vec<ReachKey>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_reach_key())
                    .or_default()
                    .push(rewrite.to_reach_key());
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for WeightedReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.queue.pop() {
            let key = match self.keys.get(entry.key_index) {
                Some(key) => key.clone(),
                None => continue,
            };
            let info = match self.term_info(&key) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&key))
                .cloned()
                .unwrap_or_default();
            for to_key in next_ids {
                if self.visited.insert(to_key.clone()) {
                    let sequence = self.next_sequence;
                    self.next_sequence = self.next_sequence.saturating_add(1);
                    let key_index = self.key_index_for(to_key);
                    self.queue.push(WeightedQueueEntry {
                        key_index,
                        weight: entry.weight,
                        sequence,
                    });
                }
            }
        }
        None
    }
}

impl AscentResults {
    /// Create empty results
    pub fn empty() -> Self {
        Self {
            all_terms: Vec::new(),
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    /// Create minimal results for a single term (e.g. after direct eval). One term, no rewrites.
    pub fn from_single_term(term: &dyn Term) -> Self {
        Self {
            all_terms: vec![TermInfo {
                term_id: term.term_id(),
                exact_key: None,
                display: format!("{}", term),
                is_normal_form: true,
            }],
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    fn term_info_by_reach_key(&self, key: &ReachKey) -> Option<&TermInfo> {
        match key {
            ReachKey::Exact(exact) => self
                .all_terms
                .iter()
                .find(|term| term.exact_key.as_ref() == Some(exact)),
            ReachKey::Legacy(id) => self.all_terms.iter().find(|term| term.term_id == *id),
        }
    }

    fn seed_reach_key(&self, seed: &RewriteSeed) -> ReachKey {
        seed.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or_else(|| ReachKey::Legacy(seed.term_id))
    }

    fn weighted_seed_reach_key(&self, seed: &WeightedRewriteSeed) -> ReachKey {
        seed.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or_else(|| ReachKey::Legacy(seed.term_id))
    }

    fn rewrite_seeds_for_legacy_id(&self, id: u64) -> Vec<RewriteSeed> {
        let mut seeds = Vec::new();
        let mut seen = HashSet::new();
        for term in self.all_terms.iter().filter(|term| term.term_id == id) {
            let seed = RewriteSeed {
                term_id: term.term_id,
                exact_key: term.exact_key.clone(),
                display: term.display.clone(),
            };
            let key = self.seed_reach_key(&seed);
            if seen.insert(key) {
                seeds.push(seed);
            }
        }
        if seeds.is_empty() {
            seeds.push(RewriteSeed::legacy(id, String::new()));
        }
        seeds
    }

    /// Lazily iterate normal forms (terms with no outgoing rewrites).
    pub fn normal_forms_iter(&self) -> impl Iterator<Item = &TermInfo> {
        self.all_terms.iter().filter(|t| t.is_normal_form)
    }

    /// Get normal forms (terms with no outgoing rewrites).
    pub fn normal_forms(&self) -> Vec<&TermInfo> {
        self.normal_forms_iter().collect()
    }

    /// Lazily iterate rewrites from a specific term.
    pub fn rewrites_from_iter(&self, term_id: u64) -> impl Iterator<Item = &Rewrite> {
        self.rewrites.iter().filter(move |r| r.from_id == term_id)
    }

    /// Get rewrites from a specific term
    pub fn rewrites_from(&self, term_id: u64) -> Vec<&Rewrite> {
        self.rewrites_from_iter(term_id).collect()
    }

    /// Find a normal form reachable from the given term by following rewrites.
    /// Returns the first normal form reached (BFS). If the start term is already
    /// a normal form, returns it. Returns `None` if the term is not in the graph.
    pub fn normal_form_reachable_from(&self, start_id: u64) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(&[start_id])
            .next()
    }

    /// Multi-source normal-form traversal.
    ///
    /// Yields every normal form reachable from the given seeds, preserving
    /// seed/BFS order. This is the ambiguity-preserving surface for consumers
    /// that receive an `Ambiguous` wrapper from parsing and need to carry all
    /// alternatives into evaluation.
    ///
    /// The rewrite adjacency index is initialized only if a non-normal seed
    /// must be expanded; asking for the first result from an already-normal
    /// seed does not scan the rewrite relation.
    pub fn normal_forms_reachable_from_seeds_iter<'a>(
        &'a self,
        seed_ids: &[u64],
    ) -> ReachableNormalForms<'a> {
        ReachableNormalForms::new(self, seed_ids)
    }

    /// Exact multi-source normal-form traversal.
    ///
    /// Prefer this over `normal_forms_reachable_from_seeds_iter` when the
    /// caller has parser/generated exact semantic keys. This is the
    /// no-loss surface: traversal identity is the exact key, falling back to
    /// `term_id` only for legacy seeds.
    pub fn normal_forms_reachable_from_rewrite_seeds_iter<'a>(
        &'a self,
        seeds: &[RewriteSeed],
    ) -> ReachableNormalForms<'a> {
        ReachableNormalForms::new_exact(self, seeds)
    }

    /// Collect all normal forms reachable from the given seeds.
    pub fn normal_forms_reachable_from_seeds(&self, seed_ids: &[u64]) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids)
            .collect()
    }

    /// Collect all normal forms reachable from exact rewrite seeds.
    pub fn normal_forms_reachable_from_rewrite_seeds(
        &self,
        seeds: &[RewriteSeed],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_rewrite_seeds_iter(seeds)
            .collect()
    }

    /// Compatibility helper for callers that explicitly want one witness.
    ///
    /// This returns the first result from the lazy multi-source traversal. It
    /// deliberately does not choose by display length or any other heuristic.
    pub fn normal_form_reachable_from_seeds(&self, seed_ids: &[u64]) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids).next()
    }

    /// Compatibility helper for callers that explicitly want one exact-seeded
    /// witness.
    pub fn normal_form_reachable_from_rewrite_seeds(
        &self,
        seeds: &[RewriteSeed],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_rewrite_seeds_iter(seeds)
            .next()
    }

    /// Multi-source normal-form traversal ordered by seed weight.
    ///
    /// This is the explicit priority-queue surface for callers that carry
    /// parser/evidence weights through to evaluation. It is demand bounded:
    /// callers can use `.take(n)` or `.next()` without collecting all reachable
    /// normal forms.
    pub fn normal_forms_reachable_from_weighted_seeds_iter<'a>(
        &'a self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> WeightedReachableNormalForms<'a> {
        WeightedReachableNormalForms::new(self, weighted_seed_ids)
    }

    /// Exact weighted normal-form traversal.
    pub fn normal_forms_reachable_from_weighted_rewrite_seeds_iter<'a>(
        &'a self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> WeightedReachableNormalForms<'a> {
        WeightedReachableNormalForms::new_exact(self, weighted_seeds)
    }

    /// Collect all normal forms reachable from weighted seeds.
    pub fn normal_forms_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .collect()
    }

    /// Collect all normal forms reachable from exact weighted seeds.
    pub fn normal_forms_reachable_from_weighted_rewrite_seeds(
        &self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_weighted_rewrite_seeds_iter(weighted_seeds)
            .collect()
    }

    /// Return the first normal form from the lazy weighted traversal.
    pub fn normal_form_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .next()
    }

    /// Return the first normal form from the exact lazy weighted traversal.
    pub fn normal_form_reachable_from_weighted_rewrite_seeds(
        &self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_weighted_rewrite_seeds_iter(weighted_seeds)
            .next()
    }

    /// Get the equivalence class containing a term
    pub fn equiv_class(&self, term_id: u64) -> Option<&EquivClass> {
        self.equivalences
            .iter()
            .find(|ec| ec.term_ids.contains(&term_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BackendCapabilityDef;

    fn reflected_chain(depth: usize) -> RuntimeReflectedSubterm {
        let mut term = RuntimeReflectedSubterm {
            constructor: "Leaf".to_string(),
            children: Vec::new(),
        };
        for _ in 0..depth {
            term = RuntimeReflectedSubterm {
                constructor: "Node".to_string(),
                children: vec![term],
            };
        }
        term
    }

    #[test]
    fn reflected_subterm_lifecycle_and_relabel_are_stack_safe() {
        let depth = 16_384;
        let mut term = reflected_chain(depth);
        let cloned = term.clone();
        assert!(term == cloned);

        term.relabel_constructors(|label| format!("Bare::{label}"));
        let mut measured = 0usize;
        let mut cursor = &term;
        loop {
            assert!(cursor.constructor.starts_with("Bare::"));
            let Some(child) = cursor.children.first() else {
                break;
            };
            measured += 1;
            cursor = child;
        }
        assert_eq!(measured, depth);

        let rendered = format!("{cloned:?}");
        assert_eq!(rendered.matches("RuntimeReflectedSubterm").count(), depth + 1);
        drop(term);
        drop(cloned);
    }

    #[test]
    fn reflected_subterm_debug_matches_derived_shape() {
        let term = RuntimeReflectedSubterm {
            constructor: "Pair".to_string(),
            children: vec![
                RuntimeReflectedSubterm {
                    constructor: "Left".to_string(),
                    children: Vec::new(),
                },
                RuntimeReflectedSubterm {
                    constructor: "Right".to_string(),
                    children: Vec::new(),
                },
            ],
        };
        assert_eq!(
            format!("{term:?}"),
            "RuntimeReflectedSubterm { constructor: \"Pair\", children: [RuntimeReflectedSubterm { constructor: \"Left\", children: [] }, RuntimeReflectedSubterm { constructor: \"Right\", children: [] }] }"
        );
    }

    #[derive(Debug, Clone)]
    struct DispatchTerm;

    impl fmt::Display for DispatchTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "dispatch")
        }
    }

    impl Term for DispatchTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            1
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other.as_any().is::<DispatchTerm>()
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct DispatchMetadata;

    static DISPATCH_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::Ascent,
        is_default: true,
    }];

    impl LanguageMetadata for DispatchMetadata {
        fn name(&self) -> &'static str {
            "Dispatch"
        }

        fn types(&self) -> &'static [crate::metadata::TypeDef] {
            &[]
        }

        fn terms(&self) -> &'static [crate::metadata::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [crate::metadata::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [crate::metadata::RewriteDef] {
            &[]
        }

        fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
            DISPATCH_BACKENDS
        }
    }

    static DISPATCH_METADATA: DispatchMetadata = DispatchMetadata;

    struct DispatchLanguage;

    impl Language for DispatchLanguage {
        fn name(&self) -> &'static str {
            "Dispatch"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &DISPATCH_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DispatchTerm))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Ok(AscentResults::empty())
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::Unknown
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    struct NoDefaultMetadata;

    impl LanguageMetadata for NoDefaultMetadata {
        fn name(&self) -> &'static str {
            "NoDefault"
        }

        fn types(&self) -> &'static [crate::metadata::TypeDef] {
            &[]
        }

        fn terms(&self) -> &'static [crate::metadata::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [crate::metadata::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [crate::metadata::RewriteDef] {
            &[]
        }

        fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
            &[]
        }
    }

    static NO_DEFAULT_METADATA: NoDefaultMetadata = NoDefaultMetadata;

    struct NoDefaultLanguage;

    impl Language for NoDefaultLanguage {
        fn name(&self) -> &'static str {
            "NoDefault"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &NO_DEFAULT_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DispatchTerm))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::Unknown
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    struct RhoDispatchMetadata;

    static RHO_DISPATCH_BACKENDS: &[BackendCapabilityDef] = &[
        BackendCapabilityDef {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
        },
        BackendCapabilityDef {
            backend: RuntimeBackend::Ascent,
            is_default: false,
        },
    ];

    impl LanguageMetadata for RhoDispatchMetadata {
        fn name(&self) -> &'static str {
            "RhoDispatch"
        }

        fn types(&self) -> &'static [crate::metadata::TypeDef] {
            &[]
        }

        fn terms(&self) -> &'static [crate::metadata::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [crate::metadata::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [crate::metadata::RewriteDef] {
            &[]
        }

        fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
            RHO_DISPATCH_BACKENDS
        }
    }

    static RHO_DISPATCH_METADATA: RhoDispatchMetadata = RhoDispatchMetadata;

    struct RhoDispatchLanguage;

    impl Language for RhoDispatchLanguage {
        fn name(&self) -> &'static str {
            "RhoDispatch"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &RHO_DISPATCH_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DispatchTerm))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Ok(AscentResults::empty())
        }

        fn run_backend_report(
            &self,
            backend: RuntimeBackend,
            _term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::Ascent => Err(format!(
                    "Ascent report execution for language {} is oracle-only; use the explicit reference helper instead of the production runtime dispatcher",
                    self.name()
                )),
                RuntimeBackend::RhoMachine => RuntimeBackendReport::try_observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Text("rho-default".to_string())],
                    )],
                )
                .map_err(|err| err.to_string()),
                other => {
                    Err(format!("{} backend is not installed for language {}", other, self.name()))
                },
            }
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::Unknown
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    fn sample_results() -> AscentResults {
        AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "start".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "mid".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 3,
                    exact_key: None,
                    display: "done".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 2,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("step1".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 3,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("step2".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    fn sample_dovetail_runtime_report() -> RuntimeDovetailRunReport {
        RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![
                RuntimeDovetailTermRecord {
                    ordinal: 0,
                    class_id: 0,
                    key: b"root".to_vec(),
                    op_display: "Pair".to_string(),
                    weight_display: "1".to_string(),
                    is_root: true,
                    source_display: None,
                },
                RuntimeDovetailTermRecord {
                    ordinal: 1,
                    class_id: 1,
                    key: b"child".to_vec(),
                    op_display: "Leaf".to_string(),
                    weight_display: "0".to_string(),
                    is_root: false,
                    source_display: None,
                },
            ],
            derivation_edges: vec![RuntimeDovetailDerivationEdge {
                ordinal: 0,
                parent_key: b"root".to_vec(),
                child_key: b"child".to_vec(),
                child_index: 0,
            }],
            rule_firings: vec![RuntimeDovetailRuleFiring {
                ordinal: 0,
                label: Some("sample-rule".to_string()),
                count: 2,
            }],
            rewrite_justifications: Vec::new(),
            declined_folds: Vec::new(),
            completeness: RuntimeDovetailCompleteness::Complete,
            graph_kind: RuntimeDovetailGraphKind::Derivation,
        }
    }

    #[test]
    fn dovetail_report_shape_validation_accepts_consistent_report() {
        let report = sample_dovetail_runtime_report();

        report
            .validate_shape()
            .expect("sample report is structurally valid");
        let backend_report = RuntimeBackendReport::try_dovetail(report)
            .expect("checked constructor accepts structurally valid Dovetail reports");

        assert_eq!(backend_report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(backend_report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_bad_root_ordinal() {
        let mut report = sample_dovetail_runtime_report();
        report.root_ordinals[0] = 99;

        let err = report
            .validate_shape()
            .expect_err("root ordinals must resolve into the term table");
        assert!(matches!(
            err,
            RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                root_index: 0,
                ordinal: 99,
                terms: 2
            }
        ));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_dangling_edges() {
        let mut report = sample_dovetail_runtime_report();
        report.derivation_edges[0].child_key = b"missing".to_vec();

        let err = RuntimeBackendReport::try_dovetail(report)
            .expect_err("checked constructor rejects dangling derivation edges");
        assert!(matches!(err, RuntimeDovetailReportError::EdgeChildMissing { edge_ordinal: 0 }));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_duplicate_term_keys() {
        let mut report = sample_dovetail_runtime_report();
        report.terms.push(RuntimeDovetailTermRecord {
            ordinal: 2,
            class_id: 2,
            key: b"child".to_vec(),
            op_display: "DuplicateLeaf".to_string(),
            weight_display: "0".to_string(),
            is_root: false,
            source_display: None,
        });

        let err = report
            .validate_shape()
            .expect_err("term records must be unique by exact key");
        assert!(matches!(err, RuntimeDovetailReportError::DuplicateTermKey { ordinal: 2 }));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_bad_rule_firing_ordinal() {
        let mut report = sample_dovetail_runtime_report();
        report.rule_firings[0].ordinal = 7;

        let err = report
            .validate_shape()
            .expect_err("bad rule-firing ordinal must be rejected");

        assert!(matches!(
            err,
            RuntimeDovetailReportError::RuleFiringOrdinalMismatch { index: 0, ordinal: 7 }
        ));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_zero_rule_firing_count() {
        let mut report = sample_dovetail_runtime_report();
        report.rule_firings[0].count = 0;

        let err = report
            .validate_shape()
            .expect_err("zero-count rule firing evidence must be rejected");

        assert!(matches!(err, RuntimeDovetailReportError::RuleFiringZeroCount { ordinal: 0 }));
    }

    #[test]
    fn observation_report_shape_validation_accepts_rho_ast_observations() {
        let report = RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            RuntimeBackendArtifact::RhoNormalizedAst,
            vec![RuntimeChannelObservation::new("OUT", vec![RuntimeObservationValue::Int(5)])],
        )
        .expect("Rho normalized AST may produce observation-shaped runtime output");

        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
        assert!(report.observations_for_channel("OUT").is_some());
    }

    #[test]
    fn observation_report_shape_validation_rejects_ascent_backend() {
        let err = RuntimeBackendReport::try_observations(
            RuntimeBackend::Ascent,
            RuntimeBackendArtifact::RhoNormalizedAst,
            Vec::new(),
        )
        .expect_err("Ascent reports must remain Ascent-shaped");

        assert!(matches!(
            err,
            RuntimeObservationReportError::InvalidObservationBackend {
                backend: RuntimeBackend::Ascent
            }
        ));
    }

    #[test]
    fn observation_report_shape_validation_rejects_non_rho_artifact() {
        let err = RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            RuntimeBackendArtifact::DovetailRunReport,
            Vec::new(),
        )
        .expect_err("Rho observations must be backed by a Rho runtime artifact");

        assert!(matches!(
            err,
            RuntimeObservationReportError::InvalidObservationArtifact {
                backend: RuntimeBackend::RhoMachine,
                artifact: RuntimeBackendArtifact::DovetailRunReport
            }
        ));
    }

    #[test]
    fn runtime_backend_dispatch_rejects_ascent_production_default() {
        let language = DispatchLanguage;
        let term = DispatchTerm;

        assert_eq!(language.metadata().runtime_backends(), DISPATCH_BACKENDS);
        assert_eq!(language.selected_default_runtime_backend(), None);
        assert_eq!(language.default_runtime_backend(), None);
        assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(language.run_ascent(&term).is_ok());

        let default_err = language
            .run_default_backend_report(&term)
            .expect_err("Ascent metadata default must not become a production default");
        assert!(
            default_err.contains("does not advertise a default runtime backend"),
            "{default_err}"
        );

        let ascent_err = language
            .run_backend_report(RuntimeBackend::Ascent, &term)
            .expect_err("Ascent report execution must be oracle-only");
        assert!(
            ascent_err.contains("Ascent report execution for language Dispatch is oracle-only"),
            "{ascent_err}"
        );

        let err = language
            .run_backend_report(RuntimeBackend::Dovetail, &term)
            .expect_err("absent Dovetail backend must not fall back to Ascent");
        assert!(err.contains("Dovetail backend is not installed for language Dispatch"));
    }

    #[test]
    fn runtime_backend_dispatch_does_not_fabricate_ascent_default() {
        let language = NoDefaultLanguage;
        let term = DispatchTerm;

        assert!(language.runtime_backend_capabilities().is_empty());
        assert_eq!(language.selected_default_runtime_backend(), None);
        assert_eq!(language.default_runtime_backend(), None);
        assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));

        let ascent_oracle_err = language
            .run_ascent(&term)
            .expect_err("languages without an explicit oracle must fail closed");
        assert!(
            ascent_oracle_err.contains("Ascent oracle for language NoDefault is not installed"),
            "{ascent_oracle_err}"
        );

        let report_err = language
            .run_default_backend_report(&term)
            .expect_err("default report execution must fail closed without a selected backend");
        assert!(
            report_err.contains("does not advertise a default runtime backend"),
            "{report_err}"
        );

        let explicit_ascent_err = language
            .run_backend_report(RuntimeBackend::Ascent, &term)
            .expect_err("explicit Ascent report execution must be oracle-only");
        assert!(
            explicit_ascent_err
                .contains("Ascent report execution for language NoDefault is oracle-only"),
            "{explicit_ascent_err}"
        );

        let seeded_err = language
            .run_default_backend_report_with_facts(&term, &SeedFacts::new())
            .expect_err("seeded default report execution must fail closed without a default");
        assert!(
            seeded_err.contains("does not advertise a default runtime backend"),
            "{seeded_err}"
        );

        let explicit_seeded_ascent_err = language
            .run_backend_report_with_facts(RuntimeBackend::Ascent, &term, &SeedFacts::new())
            .expect_err("explicit seeded Ascent report execution must be oracle-only");
        assert!(
            explicit_seeded_ascent_err
                .contains("seeded Ascent report execution for language NoDefault is oracle-only"),
            "{explicit_seeded_ascent_err}"
        );
    }

    #[test]
    fn runtime_backend_dispatch_uses_metadata_default_when_backend_is_installed() {
        let language = RhoDispatchLanguage;
        let term = DispatchTerm;

        assert_eq!(language.metadata().runtime_backends(), RHO_DISPATCH_BACKENDS);
        assert_eq!(language.selected_default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
        assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
        assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));

        let report = language
            .run_default_backend_report(&term)
            .expect("metadata-selected Rho backend must dispatch");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
        let out = report
            .observations_for_channel("OUT")
            .expect("Rho report must expose the OUT channel");
        assert_eq!(out.observed_count(), 1);
        assert_eq!(
            out.membership_fingerprint(),
            BTreeSet::from([RuntimeObservationValue::Text("rho-default".to_string())])
        );

        assert!(matches!(report.output(), RuntimeBackendOutput::Observations(_)));
    }

    #[test]
    fn normal_forms_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .normal_forms_iter()
            .map(|term| term.display.as_str())
            .collect();
        let eager: Vec<_> = results
            .normal_forms()
            .iter()
            .map(|term| term.display.as_str())
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec!["done"]);
    }

    #[test]
    fn rewrites_from_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .rewrites_from_iter(1)
            .map(|rewrite| rewrite.to_id)
            .collect();
        let eager: Vec<_> = results
            .rewrites_from(1)
            .iter()
            .map(|rewrite| rewrite.to_id)
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec![2]);
    }

    #[test]
    fn reachable_normal_form_uses_lazy_rewrite_iteration() {
        let results = sample_results();
        let nf = results
            .normal_form_reachable_from(1)
            .expect("normal form should be reachable");

        assert_eq!(nf.term_id, 3);
        assert_eq!(nf.display, "done");
    }

    #[test]
    fn reachable_normal_forms_from_seeds_preserves_ambiguous_alternatives() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "longer-but-first".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "a".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("left".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("right".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_seeds(&[1, 2])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["longer-but-first", "a"]);

        let first = results
            .normal_form_reachable_from_seeds(&[1, 2])
            .expect("at least one normal form should be reachable");
        assert_eq!(
            first.display, "longer-but-first",
            "single-witness helper must not choose the shortest display"
        );
    }

    #[test]
    fn weighted_reachable_normal_forms_choose_lower_weight_seed_first() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "higher_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "lower_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "higher_weight_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "lower_weight_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("high".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("low".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let first = results
            .normal_form_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .expect("weighted normal form should be reachable");
        assert_eq!(first.display, "lower_weight_result");

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["lower_weight_result", "higher_weight_result"]);
    }

    #[test]
    fn weighted_reachable_normal_forms_preserve_equal_weight_seed_order() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "first_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "second_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("first".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("second".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 3.0), (2, 3.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["first_result", "second_result"]);
    }

    #[test]
    fn reachable_normal_forms_use_exact_keys_despite_term_id_collision() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![0]),
                    display: "left_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![1]),
                    display: "right_seed_same_u64".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![10]),
                    display: "left_nf".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![20]),
                    display: "right_nf_same_u64".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![0]),
                    to_key: Some(vec![10]),
                    rule_name: Some("left".to_string()),
                },
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![1]),
                    to_key: Some(vec![20]),
                    rule_name: Some("right".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let exact_seeds = vec![
            RewriteSeed::exact(7, vec![0], "left_seed".to_string()),
            RewriteSeed::exact(7, vec![1], "right_seed_same_u64".to_string()),
        ];
        let exact: Vec<_> = results
            .normal_forms_reachable_from_rewrite_seeds(&exact_seeds)
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(exact, vec!["left_nf", "right_nf_same_u64"]);

        let legacy: Vec<_> = results
            .normal_forms_reachable_from_seeds(&[7])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(
            legacy,
            vec!["left_nf", "right_nf_same_u64"],
            "legacy seed ids must expand colliding ids rather than dropping a candidate"
        );
    }

    #[test]
    fn weighted_reachable_normal_forms_use_exact_keys_despite_term_id_collision() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![0]),
                    display: "slow_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![1]),
                    display: "fast_seed_same_u64".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![10]),
                    display: "slow_nf".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![20]),
                    display: "fast_nf_same_u64".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![0]),
                    to_key: Some(vec![10]),
                    rule_name: Some("slow".to_string()),
                },
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![1]),
                    to_key: Some(vec![20]),
                    rule_name: Some("fast".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let exact_seeds = vec![
            WeightedRewriteSeed::exact(7, vec![0], "slow_seed".to_string(), 5.0),
            WeightedRewriteSeed::exact(7, vec![1], "fast_seed_same_u64".to_string(), 1.0),
        ];
        let exact: Vec<_> = results
            .normal_forms_reachable_from_weighted_rewrite_seeds(&exact_seeds)
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(exact, vec!["fast_nf_same_u64", "slow_nf"]);
    }
}
