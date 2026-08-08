//! Phase 4 #5b (2026-05-12): Class-2 HashMap binder smoke test.
//!
//! Validates that a Class-2 binder rule with a `HashMap(K, V)` SimpleCollection
//! slot parses correctly end-to-end through the WPDS walker. The walker's
//! 3-phase `kv_phase` dispatch handles:
//! - phase 0: outer dispatch (close / inter-pair-sep / first-key element)
//! - phase 1: Consume the key/value separator `:` (HashMap only)
//! - phase 2: Push CategoryEntry for the value parse (HashMap only)
//!
//! Empty `( )` exercises phase 0's close branch only — same as the empty-only
//! pilot from Phase 4 #5 (commit `5bb9409`). Non-empty exercises the full
//! cycle, where `cursor.collection_stack[acc_id].len()` parity drives
//! `kv_phase` transitions via `set_cursor_inner_state`.
//!
//! Test predictions:
//! - PRED-1 empty `chooseMap 0 ( )` → `ChooseMap(Box<PZero>, {})`.
//! - PRED-2 singleton `chooseMap 0 ( 0 : 0 )` → `ChooseMap(Box<PZero>, {PZero: PZero})`.
//! - PRED-3 two identical pairs `chooseMap 0 ( 0 : 0 , 0 : 0 )` →
//!     `ChooseMap(Box<PZero>, {PZero: PZero})` (HashMap dedups identical
//!     keys so post-parse len remains 1).
//!
//! Caveat: deep nesting (3+ levels of `chooseMap` in value position) can
//! lose the innermost entry due to a pre-existing parser issue with
//! strict-mode Fork-branch exploration of nested HashMap values. The
//! auto-generated prop test
//! `gen_class2hashmapsmoke_prop::proc_display_parse_roundtrip`
//! triggers this for randomly-generated deep terms; the 3 PRED-N
//! prediction tests above cover the Phase 4 #5b feature contract
//! (key/value separator parsing + parity-driven kv_phase) and pass
//! cleanly. 2-level nested cases (e.g. `chooseMap 0 ( 0 : chooseMap 0
//! ( 0 : 0 ) )`) also pass.

// Task #11 (extended 2026-07-26): `Class2HashMapSmoke` is a FIXTURE grammar, not a production
// language, so its definition lives in `languages/tests/definitions/class2hashmapsmoke.rs` rather
// than in the `languages` library (`languages/src/` is production-only).
//
// This file is its DESIGNATED HOST: it declares the definition module and is the one and
// only invoker of the opt-in `class2hashmapsmoke_generated_tests!` wrapper, which materializes the
// macro-generated unit / prop / analytical sections that used to be written to
// `languages/tests/gen_class2hashmapsmoke_*.rs`. Other consumers `#[path]`-include the same definition
// WITHOUT invoking the wrapper, so the generated tests exist exactly once across the suite.
#[path = "definitions/class2hashmapsmoke.rs"]
mod class2hashmapsmoke;

class2hashmapsmoke::class2hashmapsmoke_generated_tests!(crate::class2hashmapsmoke);

use class2hashmapsmoke::Proc;
use mettail_runtime::FramedSemanticKeyHasher;
use std::hash::Hash;

/// Bounded, recursively derived oracle for the generated iterative `Debug`.
/// It deliberately lives in the test host and rebuilds the fixture's recursive
/// shape into an ordinary `#[derive(Debug)]` enum; production code never calls
/// it, and deep-stack tests exercise the generated PDA directly.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ProcDebugOracle {
    PZero,
    ChooseMap(
        Box<ProcDebugOracle>,
        mettail_runtime::HashMapLit<ProcDebugOracle, ProcDebugOracle>,
    ),
}

impl Hash for ProcDebugOracle {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::PZero => 0usize.hash(state),
            Self::ChooseMap(head, entries) => {
                1usize.hash(state);
                head.hash(state);
                entries.hash(state);
            },
        }
    }
}

fn proc_debug_oracle(proc: &Proc) -> ProcDebugOracle {
    match proc {
        Proc::PZero => ProcDebugOracle::PZero,
        Proc::ChooseMap(head, entries) => ProcDebugOracle::ChooseMap(
            Box::new(proc_debug_oracle(head)),
            entries
                .iter()
                .map(|(key, value)| (proc_debug_oracle(key), proc_debug_oracle(value)))
                .collect(),
        ),
        other => panic!(
            "Class2HashMapSmoke Debug oracle received an undeclared fixture shape: {other:?}"
        ),
    }
}

fn hash_stream<T: Hash>(value: &T) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    value.hash(&mut hasher);
    hasher.into_key()
}

fn semantic_hash_stream(value: &Proc) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    value.semantic_hash(&mut hasher);
    hasher.into_key()
}

fn nested_map_value_spine(depth: usize) -> Proc {
    let mut term = Proc::PZero;
    for _ in 0..depth {
        let mut entries = mettail_runtime::HashMapLit::new();
        entries.insert(Proc::PZero, term);
        term = Proc::ChooseMap(std::sync::Arc::new(Proc::PZero), entries);
    }
    term
}

#[test]
fn pred1_empty_map() {
    let result = Proc::parse_via_wpda("chooseMap 0 ( )").expect("'chooseMap 0 ( )' parses");
    match &result {
        Proc::ChooseMap(_a, ms) => {
            assert_eq!(ms.len(), 0, "ms should be empty");
        },
        other => panic!("expected Proc::ChooseMap, got {:?}", other),
    }
}

#[test]
fn pred2_singleton_pair() {
    let result =
        Proc::parse_via_wpda("chooseMap 0 ( 0 : 0 )").expect("'chooseMap 0 ( 0 : 0 )' parses");
    match &result {
        Proc::ChooseMap(_a, ms) => {
            assert_eq!(ms.len(), 1, "ms should have one entry");
        },
        other => panic!("expected Proc::ChooseMap, got {:?}", other),
    }
}

#[test]
fn pred3_two_pairs() {
    let result = Proc::parse_via_wpda("chooseMap 0 ( 0 : 0 , 0 : 0 )")
        .expect("'chooseMap 0 ( 0 : 0 , 0 : 0 )' parses");
    match &result {
        Proc::ChooseMap(_a, ms) => {
            // HashMap dedups identical keys: PZero -> PZero inserted twice
            // collapses to a single entry. Length remains 1.
            assert_eq!(ms.len(), 1, "ms should have one entry (dedup PZero key)");
        },
        other => panic!("expected Proc::ChooseMap, got {:?}", other),
    }
}

#[test]
fn iterative_debug_matches_derive_for_hashmaps_in_both_layouts() {
    for source in [
        "0",
        "chooseMap 0 ( )",
        "chooseMap 0 ( 0 : 0 )",
        "chooseMap 0 ( 0 : chooseMap 0 ( ) )",
        "chooseMap chooseMap 0 ( ) ( chooseMap 0 ( ) : 0 )",
    ] {
        let term = Proc::parse_via_wpda(source).unwrap_or_else(|error| {
            panic!("Debug oracle fixture `{source}` failed to parse: {error}")
        });
        let oracle = proc_debug_oracle(&term);

        assert_eq!(
            format!("{term:?}"),
            format!("{oracle:?}"),
            "compact generated Debug diverged from derive for `{source}`"
        );
        assert_eq!(
            format!("{term:#?}"),
            format!("{oracle:#?}"),
            "alternate generated Debug diverged from derive for `{source}`"
        );
    }
}

#[test]
fn iterative_eq_ord_and_hash_match_recursive_derive_for_hashmaps() {
    let sources = [
        "0",
        "chooseMap 0 ( )",
        "chooseMap 0 ( 0 : 0 )",
        "chooseMap 0 ( 0 : chooseMap 0 ( ) )",
        "chooseMap chooseMap 0 ( ) ( chooseMap 0 ( ) : 0 )",
    ];
    let terms: Vec<Proc> = sources
        .iter()
        .map(|source| {
            Proc::parse_via_wpda(source).unwrap_or_else(|error| {
                panic!("comparison oracle fixture `{source}` failed to parse: {error}")
            })
        })
        .collect();
    let oracles: Vec<ProcDebugOracle> = terms.iter().map(proc_debug_oracle).collect();

    for (index, (term, oracle)) in terms.iter().zip(&oracles).enumerate() {
        assert_eq!(
            proc_debug_oracle(&term.clone()),
            oracle.clone(),
            "generated Clone diverged from recursive derive at `{}`",
            sources[index]
        );
        assert_eq!(
            hash_stream(term),
            hash_stream(oracle),
            "generated Hash changed derive's framed write stream at `{}`",
            sources[index]
        );

        for (other_index, (other_term, other_oracle)) in terms.iter().zip(&oracles).enumerate() {
            assert_eq!(
                term == other_term,
                oracle == other_oracle,
                "generated Eq diverged from derive for (`{}`, `{}`)",
                sources[index],
                sources[other_index]
            );
            assert_eq!(
                term.cmp(other_term),
                oracle.cmp(other_oracle),
                "generated Ord diverged from derive for (`{}`, `{}`)",
                sources[index],
                sources[other_index]
            );
        }
    }
}

const DEEP_TRAIT_DEPTH: usize = 20_000;

fn on_256k_stack(name: &str, operation: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(256 * 1024)
        .spawn(operation)
        .expect("the OS must create the constrained generated-trait thread")
        .join()
        .expect("a generated trait overflowed or panicked on a 256 KiB stack");
}

#[test]
fn generated_drop_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-drop-256k", || {
        drop(nested_map_value_spine(DEEP_TRAIT_DEPTH));
    });
}

#[test]
fn generated_clone_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-clone-256k", || {
        let original = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let cloned = original.clone();
        drop(cloned);
        drop(original);
    });
}

#[test]
fn generated_eq_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-eq-256k", || {
        let left = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let right = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        assert!(left == right, "deep generated Eq changed its result");
    });
}

#[test]
fn generated_ord_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-ord-256k", || {
        let left = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let right = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        assert_eq!(
            left.cmp(&right),
            std::cmp::Ordering::Equal,
            "deep generated Ord changed its result"
        );
    });
}

#[test]
fn generated_hash_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-hash-256k", || {
        let left = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let right = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        assert_eq!(
            hash_stream(&left),
            hash_stream(&right),
            "deep equal values violated Hash's equality contract"
        );
    });
}

#[test]
fn generated_semantic_hash_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-semantic-hash-256k", || {
        let left = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let right = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        assert_eq!(
            semantic_hash_stream(&left),
            semantic_hash_stream(&right),
            "deep equal values changed the semantic-hash stream"
        );
    });
}

#[test]
fn generated_debug_survives_a_deep_hashmap_value_spine_on_256k() {
    on_256k_stack("generated-hashmap-debug-256k", || {
        let value = nested_map_value_spine(DEEP_TRAIT_DEPTH);
        let compact = format!("{value:?}");
        assert!(
            compact.starts_with("ChooseMap(PZero, HashMapLit({PZero: ChooseMap("),
            "deep compact Debug lost the recursive HashMap structure"
        );
        assert_eq!(
            compact.matches("ChooseMap(").count(),
            DEEP_TRAIT_DEPTH,
            "deep compact Debug omitted or duplicated a recursive enum layer"
        );
        assert_eq!(
            compact.matches("HashMapLit({").count(),
            DEEP_TRAIT_DEPTH,
            "deep compact Debug omitted or duplicated a map layer"
        );
        assert!(
            compact.ends_with("))"),
            "deep compact Debug was truncated before the outer tuple fields closed"
        );

        let alternate = format!("{:#?}", nested_map_value_spine(256));
        assert!(
            alternate.contains("HashMapLit(\n") && alternate.contains("PZero: ChooseMap(\n"),
            "alternate Debug lost its derived multiline collection layout"
        );
    });
}
