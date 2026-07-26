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
