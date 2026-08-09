//! Exact, stack-safe migration gates for historical Rholang counterexamples.

use mettail_testkit::corpus_migration::{
    migrate_rholang_corpus, migrate_rholang_method_calls, CorpusMigrationError,
    RholangCorpusMigration, RholangCorpusMigrationError,
};
use mettail_testkit::ctor::{parse_debug_value, render_debug, DebugNode};

#[test]
fn method_collapse_preserves_receiver_argument_order_and_nested_calls() {
    let mut node = parse_debug_value("MSet(MKeys(PZero), LNth(PZero, PZero), MSize(PZero))")
        .expect("historical method tree parses");
    assert_eq!(migrate_rholang_method_calls(&mut node), Ok(4));
    assert_eq!(
        render_debug(&node),
        "MethodCall(MethodCall(PZero, \"keys\", []), \"set\", [MethodCall(PZero, \"nth\", [PZero]), MethodCall(PZero, \"size\", [])])"
    );
}

#[test]
fn method_collapse_rejects_historical_arity_drift() {
    let mut node = parse_debug_value("MSet(PZero, PZero)").expect("historical call parses");
    assert_eq!(
        migrate_rholang_method_calls(&mut node),
        Err(CorpusMigrationError {
            constructor: "MSet".to_string(),
            expected_arity: 3,
            actual_arity: 2,
        })
    );
}

#[test]
fn empty_legacy_byte_carrier_has_one_exact_successor() {
    let mut node = parse_debug_value("CastBytes(ListLit([]))").expect("legacy carrier parses");
    assert_eq!(
        migrate_rholang_corpus(&mut node),
        Ok(RholangCorpusMigration {
            method_calls: 0,
            byte_carriers: 1,
            pathmap_empty_carriers: 0,
        })
    );
    assert_eq!(render_debug(&node), "CastBytes(BytesLit([]))");
}

#[test]
fn untagged_empty_pathmap_has_one_mode_neutral_successor() {
    let mut node = parse_debug_value("PathmapLit(PathMapLit(HashMapLit({})))")
        .expect("legacy path-map carrier parses");
    assert_eq!(
        migrate_rholang_corpus(&mut node),
        Ok(RholangCorpusMigration {
            method_calls: 0,
            byte_carriers: 0,
            pathmap_empty_carriers: 1,
        })
    );
    assert_eq!(render_debug(&node), "PathmapLit(Empty)");
}

#[test]
fn untagged_nonempty_pathmap_mode_is_not_guessed() {
    let mut node = parse_debug_value("PathMapLit(HashMapLit({PZero: PZero}))")
        .expect("legacy path-map carrier parses");
    assert_eq!(
        migrate_rholang_corpus(&mut node),
        Err(RholangCorpusMigrationError::NonemptyLegacyPathMap { entry_count: 1 })
    );
}

#[test]
fn nonempty_process_list_is_not_guessed_into_bytes() {
    let mut node = parse_debug_value("CastBytes(ListLit([PZero]))").expect("legacy carrier parses");
    assert_eq!(
        migrate_rholang_corpus(&mut node),
        Err(RholangCorpusMigrationError::NonemptyLegacyByteList { element_count: 1 })
    );
}

#[test]
fn corpus_migration_handles_twenty_thousand_nested_calls_on_a_small_stack() {
    std::thread::Builder::new()
        .name("corpus-migration-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut node = DebugNode::Ident("PZero".to_string());
            for _ in 0..DEPTH {
                node = DebugNode::Call {
                    head: "MKeys".to_string(),
                    args: vec![node],
                };
            }
            assert_eq!(migrate_rholang_method_calls(&mut node), Ok(DEPTH));

            let mut cursor = &node;
            let mut measured = 0usize;
            while let DebugNode::Call { head, args } = cursor {
                assert_eq!(head, "MethodCall");
                cursor = &args[0];
                measured += 1;
            }
            assert_eq!(measured, DEPTH);
        })
        .expect("small-stack migration thread spawns")
        .join()
        .expect("iterative corpus migration does not overflow a 256 KiB stack");
}
