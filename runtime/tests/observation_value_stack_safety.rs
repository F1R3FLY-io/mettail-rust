//! Differential and deep-shape witnesses for `RuntimeObservationValue`'s explicit PDAs.
//!
//! Bounded assertions may use the ordinary derived operations as executable oracles. Deep
//! witnesses inspect structure iteratively so the test itself never supplies the native
//! recursion the production implementation is meant to eliminate.

use mettail_runtime::RuntimeObservationValue as V;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

/// The pre-conversion derive semantics, deliberately recursive and test-only.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum DerivedOracle {
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
    List(Vec<DerivedOracle>),
    Tuple(Vec<DerivedOracle>),
    Set(Vec<DerivedOracle>),
    Map(Vec<(DerivedOracle, DerivedOracle)>),
    Bag(Vec<(DerivedOracle, usize)>),
    Term {
        constructor: String,
        children: Vec<DerivedOracle>,
    },
}

fn derived_oracle(value: &V) -> DerivedOracle {
    match value {
        V::Int(value) => DerivedOracle::Int(*value),
        V::Bool(value) => DerivedOracle::Bool(*value),
        V::Text(value) => DerivedOracle::Text(value.clone()),
        V::TermDisplay(value) => DerivedOracle::TermDisplay(value.clone()),
        V::Bytes(value) => DerivedOracle::Bytes(value.clone()),
        V::Uri(value) => DerivedOracle::Uri(value.clone()),
        V::DoubleBits(value) => DerivedOracle::DoubleBits(*value),
        V::BigIntBytes(value) => DerivedOracle::BigIntBytes(value.clone()),
        V::BigRationalBytes { numerator, denominator } => DerivedOracle::BigRationalBytes {
            numerator: numerator.clone(),
            denominator: denominator.clone(),
        },
        V::FixedPointBytes { unscaled, scale } => DerivedOracle::FixedPointBytes {
            unscaled: unscaled.clone(),
            scale: *scale,
        },
        V::PrivateName(value) => DerivedOracle::PrivateName(value.clone()),
        V::DeployId(value) => DerivedOracle::DeployId(value.clone()),
        V::DeployerId(value) => DerivedOracle::DeployerId(value.clone()),
        V::SysAuthToken => DerivedOracle::SysAuthToken,
        V::List(values) => DerivedOracle::List(values.iter().map(derived_oracle).collect()),
        V::Tuple(values) => DerivedOracle::Tuple(values.iter().map(derived_oracle).collect()),
        V::Set(values) => DerivedOracle::Set(values.iter().map(derived_oracle).collect()),
        V::Map(entries) => DerivedOracle::Map(
            entries
                .iter()
                .map(|(key, value)| (derived_oracle(key), derived_oracle(value)))
                .collect(),
        ),
        V::Bag(entries) => DerivedOracle::Bag(
            entries
                .iter()
                .map(|(value, count)| (derived_oracle(value), *count))
                .collect(),
        ),
        V::Term { constructor, children } => DerivedOracle::Term {
            constructor: constructor.clone(),
            children: children.iter().map(derived_oracle).collect(),
        },
        _ => panic!("bounded oracle must be extended for a new observation variant"),
    }
}

fn recursive_display(value: &V) -> String {
    match value {
        V::Int(value) => value.to_string(),
        V::Bool(value) => value.to_string(),
        V::Text(value) => format!("{value:?}"),
        V::TermDisplay(value) => value.clone(),
        V::Bytes(value) => format!("0x{}", hex(value)),
        V::Uri(value) => format!("Uri({value:?})"),
        V::DoubleBits(value) => format!("DoubleBits(0x{value:016x})"),
        V::BigIntBytes(value) => format!("BigInt(0x{})", hex(value)),
        V::BigRationalBytes { numerator, denominator } => {
            format!("BigRat(0x{}/0x{})", hex(numerator), hex(denominator))
        },
        V::FixedPointBytes { unscaled, scale } => {
            format!("FixedPoint(0x{} scale {scale})", hex(unscaled))
        },
        V::PrivateName(value) => format!("Private(0x{})", hex(value)),
        V::DeployId(value) => format!("DeployId(0x{})", hex(value)),
        V::DeployerId(value) => format!("DeployerId(0x{})", hex(value)),
        V::SysAuthToken => "SysAuthToken".into(),
        V::List(values) => recursive_sequence("[", values, "]"),
        V::Tuple(values) => recursive_sequence("(", values, ")"),
        V::Set(values) => recursive_sequence("Set{", values, "}"),
        V::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| {
                    format!("{}: {}", recursive_display(key), recursive_display(value))
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        V::Bag(entries) => format!(
            "Bag{{{}}}",
            entries
                .iter()
                .map(|(value, count)| format!("{} * {count}", recursive_display(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        V::Term { constructor, children } if children.is_empty() => constructor.clone(),
        V::Term { constructor, children } => {
            format!("{constructor}{}", recursive_sequence("(", children, ")"))
        },
        _ => panic!("bounded display oracle must be extended for a new observation variant"),
    }
}

fn recursive_sequence(open: &str, values: &[V], close: &str) -> String {
    format!(
        "{open}{}{close}",
        values
            .iter()
            .map(recursive_display)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .concat()
}

fn hash_of(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn bounded_corpus() -> Vec<V> {
    vec![
        V::Int(-1),
        V::Int(0),
        V::Bool(false),
        V::Bool(true),
        V::Text("a".into()),
        V::Text("text".into()),
        V::TermDisplay("surface".into()),
        V::TermDisplay("surface-2".into()),
        V::Bytes(vec![0, 1]),
        V::Bytes(vec![0, 1, 255]),
        V::Uri("rho:id:test".into()),
        V::Uri("rho:id:test-2".into()),
        V::DoubleBits(0x3ff0_0000_0000_0000),
        V::DoubleBits(0x4000_0000_0000_0000),
        V::BigIntBytes(vec![2]),
        V::BigIntBytes(vec![2, 0]),
        V::BigRationalBytes { numerator: vec![3], denominator: vec![4] },
        V::BigRationalBytes { numerator: vec![3], denominator: vec![5] },
        V::FixedPointBytes { unscaled: vec![5], scale: 6 },
        V::FixedPointBytes { unscaled: vec![5], scale: 7 },
        V::PrivateName(vec![7]),
        V::PrivateName(vec![7, 0]),
        V::DeployId(vec![8]),
        V::DeployId(vec![8, 0]),
        V::DeployerId(vec![9]),
        V::DeployerId(vec![9, 0]),
        V::SysAuthToken,
        V::List(vec![V::Int(1), V::List(vec![V::Bool(false)])]),
        // Lexicographic sequence order must inspect the first element before length.
        V::List(vec![V::Int(2)]),
        V::List(vec![V::Int(1), V::Int(9)]),
        V::Tuple(vec![V::Text("x".into()), V::Int(2)]),
        V::Tuple(Vec::new()),
        V::Set(vec![V::Int(3), V::Int(4)]),
        V::Set(vec![V::Int(3), V::Int(5)]),
        V::Map(vec![(V::Text("k".into()), V::List(vec![V::Int(5)]))]),
        V::Map(vec![(V::Text("k".into()), V::List(vec![V::Int(6)]))]),
        V::Map(vec![(V::Text("l".into()), V::List(vec![V::Int(5)]))]),
        V::Bag(vec![(V::Tuple(vec![V::Int(6)]), 7)]),
        V::Bag(vec![(V::Tuple(vec![V::Int(6)]), 8)]),
        V::Bag(vec![(V::Tuple(vec![V::Int(7)]), 7)]),
        V::Term {
            constructor: "Node".into(),
            children: vec![V::Term {
                constructor: "Leaf".into(),
                children: Vec::new(),
            }],
        },
        V::Term {
            constructor: "Node".into(),
            children: vec![V::Int(1)],
        },
        V::Term {
            constructor: "Other".into(),
            children: Vec::new(),
        },
    ]
}

#[test]
fn clone_pda_matches_the_bounded_structural_oracle() {
    for (row, value) in bounded_corpus().iter().enumerate() {
        assert_eq!(
            derived_oracle(&value.clone()),
            derived_oracle(value),
            "clone mismatch at corpus row {row}"
        );
    }
}

#[test]
fn comparison_hash_debug_and_display_match_the_bounded_recursive_oracles() {
    let corpus = bounded_corpus();
    let oracle = corpus.iter().map(derived_oracle).collect::<Vec<_>>();
    for (left_row, left) in corpus.iter().enumerate() {
        assert_eq!(format!("{left:?}"), format!("{:?}", oracle[left_row]));
        assert_eq!(format!("{left:#?}"), format!("{:#?}", oracle[left_row]));
        assert_eq!(left.to_string(), recursive_display(left));
        assert_eq!(hash_of(left), hash_of(&oracle[left_row]));
        for (right_row, right) in corpus.iter().enumerate() {
            assert_eq!(
                left.cmp(right),
                oracle[left_row].cmp(&oracle[right_row]),
                "ordering mismatch at rows ({left_row}, {right_row})"
            );
            assert_eq!(
                left == right,
                oracle[left_row] == oracle[right_row],
                "equality mismatch at rows ({left_row}, {right_row})"
            );
        }
    }
}

#[test]
fn clone_and_drop_survive_a_deep_observation_tree() {
    const DEPTH: usize = 32_768;

    let mut value = V::Int(1);
    for _ in 0..DEPTH {
        value = V::Term {
            constructor: "Next".into(),
            children: vec![value],
        };
    }

    let cloned = value.clone();
    let equal = value.clone();
    assert_eq!(value.cmp(&equal), std::cmp::Ordering::Equal);
    assert_eq!(hash_of(&value), hash_of(&equal));

    let mut greater = value.clone();
    let mut leaf = &mut greater;
    while let V::Term { children, .. } = leaf {
        let [child] = children.as_mut_slice() else {
            panic!("deep ordering witness changed unary arity");
        };
        leaf = child;
    }
    *leaf = V::Int(2);
    assert!(value < greater);

    let mut cursor = &cloned;
    let mut observed_depth = 0usize;
    while let V::Term { constructor, children } = cursor {
        assert_eq!(constructor, "Next");
        let [child] = children.as_slice() else {
            panic!("deep clone changed unary arity at level {observed_depth}");
        };
        observed_depth += 1;
        cursor = child;
    }
    assert_eq!(observed_depth, DEPTH);
    assert!(matches!(cursor, V::Int(1)));

    let displayed = value.to_string();
    assert!(displayed.starts_with("Next(") && displayed.ends_with(')'));
    let debugged = format!("{value:?}");
    assert!(debugged.starts_with("Term { constructor: \"Next\", children: ["));
    assert!(debugged.ends_with("] }"));

    // All trees are dropped here. The old derived destructor overflowed a normal libtest thread;
    // the explicit destructor drains them through heap work stacks.
}
