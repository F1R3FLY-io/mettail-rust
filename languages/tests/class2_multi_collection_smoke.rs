//! Phase 4 #1 (2026-05-11): multi-collection-slot Class 2 smoke test.
//!
//! Validates that a Class 2 binder rule with TWO SimpleCollection slots
//! parses correctly end-to-end through the WPDS walker. The two `Vec(Proc)`
//! slots get distinct `slot_idx` values stamped into their respective
//! CollectionMarker.bp fields at codegen time, and the 3-tuple-keyed
//! per-slot lookups (close, sep, element_src) disambiguate them.
//!
//! Test predictions:
//! - PRED-1: empty/empty `pair ( ) ( )` → `Pair([], [])`.
//! - PRED-2: first singleton `pair ( 0 ) ( )` → `Pair([Zero], [])`.
//! - PRED-3: second singleton `pair ( ) ( 0 )` → `Pair([], [Zero])`.
//! - PRED-4: both non-empty `pair ( 0 | 0 ) ( 0 )` → `Pair([Zero, Zero], [Zero])`.

use mettail_languages::class2multi::Proc;

#[test]
fn pred1_both_empty() {
    let result = Proc::parse_via_wpda("pair ( ) ( )")
        .expect("empty-empty Pair parses");
    match &result {
        Proc::Pair(xs, ys) => {
            assert_eq!(xs.len(), 0, "xs should be empty");
            assert_eq!(ys.len(), 0, "ys should be empty");
        }
        other => panic!("expected Proc::Pair([], []), got {:?}", other),
    }
}

#[test]
fn pred2_first_singleton() {
    let result = Proc::parse_via_wpda("pair ( 0 ) ( )")
        .expect("singleton-empty Pair parses");
    match &result {
        Proc::Pair(xs, ys) => {
            assert_eq!(xs.len(), 1);
            assert!(matches!(&xs[0], Proc::PZero));
            assert_eq!(ys.len(), 0);
        }
        other => panic!("expected Proc::Pair([_], []), got {:?}", other),
    }
}

#[test]
fn pred3_second_singleton() {
    let result = Proc::parse_via_wpda("pair ( ) ( 0 )")
        .expect("empty-singleton Pair parses");
    match &result {
        Proc::Pair(xs, ys) => {
            assert_eq!(xs.len(), 0);
            assert_eq!(ys.len(), 1);
            assert!(matches!(&ys[0], Proc::PZero));
        }
        other => panic!("expected Proc::Pair([], [_]), got {:?}", other),
    }
}

#[test]
fn pred4_both_nonempty() {
    let result = Proc::parse_via_wpda("pair ( 0 | 0 ) ( 0 )")
        .expect("nonempty-nonempty Pair parses");
    match &result {
        Proc::Pair(xs, ys) => {
            assert_eq!(xs.len(), 2);
            for x in xs.iter() {
                assert!(matches!(x, Proc::PZero));
            }
            assert_eq!(ys.len(), 1);
            assert!(matches!(&ys[0], Proc::PZero));
        }
        other => panic!("expected Proc::Pair([_, _], [_]), got {:?}", other),
    }
}
