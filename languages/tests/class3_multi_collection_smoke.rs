//! Phase 4 #2 (2026-05-12): Class-3 + Class-2 multi-collection-slot smoke
//! test for `TaggedInputs`.
//!
//! Validates that a binder rule with a Class-3 ZIP-MAP-SEP BinderListLoop
//! AND a Class-2 SimpleCollection sibling slot parses end-to-end through
//! the WPDS walker. The per-(src, rule, slot_idx) predicate
//! `is_class3_collection_per_slot` is what makes this work; pre-Phase-4-#2
//! the per-rule `is_class3_collection` would have spuriously opened a
//! BinderScope on the Class-2 slot's CollectionMarker push.
//!
//! Test predictions:
//! - PRED-1: empty tags + empty binders + 0 body
//!   `with [ ] ( ) . { 0 }` → TaggedInputs(tags=[], ns=[], scope=...)
//! - PRED-2: nonempty tags + empty binders
//!   `with [ 0 ; 0 ] ( ) . { 0 }` → TaggedInputs(tags=[PZero, PZero], ns=[], scope=...)
//! - PRED-3: empty tags + single binder + body
//!   `with [ ] ( @(0) ? x ) . { 0 }` → TaggedInputs(tags=[], ns=[NQuote(PZero)], scope=...)
//! - PRED-4: nonempty both
//!   `with [ 0 ] ( @(0) ? x ) . { 0 }` → TaggedInputs(tags=[PZero], ns=[NQuote(PZero)], scope=...)

use mettail_languages::class3multi::Proc;

#[test]
fn pred1_all_empty() {
    let result = Proc::parse_via_wpda("with [ ] ( ) . { 0 }")
        .expect("empty-tags empty-names TaggedInputs parses");
    match &result {
        Proc::TaggedInputs(tags, ns, _scope) => {
            assert_eq!(tags.len(), 0, "tags should be empty");
            assert_eq!(ns.len(), 0, "ns should be empty");
        }
        other => panic!("expected Proc::TaggedInputs([], [], _), got {:?}", other),
    }
}

#[test]
fn pred2_nonempty_tags_empty_binders() {
    let result = Proc::parse_via_wpda("with [ 0 ; 0 ] ( ) . { 0 }")
        .expect("nonempty-tags empty-names TaggedInputs parses");
    match &result {
        Proc::TaggedInputs(tags, ns, _scope) => {
            assert_eq!(tags.len(), 2, "tags should have 2 elements");
            for t in tags.iter() {
                assert!(matches!(t, Proc::PZero));
            }
            assert_eq!(ns.len(), 0, "ns should be empty");
        }
        other => panic!("expected Proc::TaggedInputs([_, _], [], _), got {:?}", other),
    }
}

#[test]
fn pred3_empty_tags_single_binder() {
    let result = Proc::parse_via_wpda("with [ ] ( @(0) ? x ) . { 0 }")
        .expect("empty-tags single-name TaggedInputs parses");
    match &result {
        Proc::TaggedInputs(tags, ns, _scope) => {
            assert_eq!(tags.len(), 0, "tags should be empty");
            assert_eq!(ns.len(), 1, "ns should have 1 element");
        }
        other => panic!("expected Proc::TaggedInputs([], [_], _), got {:?}", other),
    }
}

#[test]
fn pred4_both_nonempty() {
    let result = Proc::parse_via_wpda("with [ 0 ] ( @(0) ? x ) . { 0 }")
        .expect("nonempty TaggedInputs parses");
    match &result {
        Proc::TaggedInputs(tags, ns, _scope) => {
            assert_eq!(tags.len(), 1, "tags should have 1 element");
            assert!(matches!(&tags[0], Proc::PZero));
            assert_eq!(ns.len(), 1, "ns should have 1 element");
        }
        other => panic!("expected Proc::TaggedInputs([_], [_], _), got {:?}", other),
    }
}
