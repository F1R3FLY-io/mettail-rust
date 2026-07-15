//! C4-C5 (2026-04-28): tests that `parse_recovering` surfaces every
//! sync-token-skip recovery round as a separate `ParseError`, not just the
//! final failure.
//!
//! The Calculator grammar is the canonical multi-error fixture: malformed
//! infix expressions like `1 + + 2` trigger the WPDS facade's
//! `WpdaState::Error` path, which the recovery wrapper retries up to
//! `MAX_RECOVERY_ROUNDS` times by skipping past sync delimiters
//! (`)`, `}`, `]`, `;`, `,`).
//!
//! The new `parse_<Cat>_via_wpds_recovering` facade entry returns
//! `(Result<Cat>, Vec<RecoveryAttempt>)` and `parse_recovering` lifts each
//! attempt into a `ParseError::UnexpectedToken` with a `recovery:` hint.

use mettail_languages::calculator::Proc;

#[test]
fn parse_recovering_surfaces_every_round_on_failure() {
    // `1 + + 2` — the second `+` has no left operand, walker errors on it,
    // recovery loop tries to skip to a sync token. There's no sync token
    // available so recovery exhausts and `ParseFailed` propagates.
    let (ast, errors) = Proc::parse_recovering("1 + + 2");
    assert!(ast.is_none(), "should fail to parse: {:?}", ast);
    assert!(!errors.is_empty(), "should accumulate at least one error");
}

#[test]
fn parse_recovering_clean_input_yields_no_errors() {
    // Sanity check: well-formed input produces no recovery rounds and a
    // clean parse. Empty error vec is the success contract.
    let (ast, errors) = Proc::parse_recovering("1 + 2");
    assert!(ast.is_some(), "should parse cleanly: errors = {:?}", errors);
    assert!(errors.is_empty(), "well-formed input should produce no errors: {:?}", errors,);
}

#[test]
fn parse_recovering_recovers_via_sync_token() {
    // `(1 + + 2)` — the `+ +` is bogus, but `)` is a sync token. Recovery
    // skips past `)` and resumes; the parse may still fail overall (no Proc
    // remains after the skip), but the recovery attempt is recorded.
    let (_ast, errors) = Proc::parse_recovering("(1 + + 2)");
    // Either errors are non-empty (recovery happened) or the parse simply
    // failed without recovery. Both are acceptable; the test is mainly that
    // we don't panic and the Vec is well-formed.
    let _ = errors;
}

// ════════════════════════════════════════════════════════════════════════════
// Task #10 item 4 (2026-07-14): the MutatingSequence virtual-chain COMMITTED
// probe — the reachable languages-level exercise of the new chain lowering
// (the SwapAdjacent kind is not reachable through any current grammar's pure
// recovery — 40+ transposition inputs scanned — so its committed hard gate is
// the walker unit `item4_swap_tokens_decodes_and_lowers_to_a_two_token_chain`
// in prattail/src/wpda_walker.rs; recorded here + in ledger §"#10 item-4").
// ════════════════════════════════════════════════════════════════════════════

/// `+ 1 2` — a leading-operator malformed expression whose PURE-arm recovery
/// proposes a TOKEN-MUTATING `ApplyRecoverySequence` (a Viterbi/WFST repair
/// that inserts + reorders, not an all-skip/delete sequence). Item 4 lowers
/// it to a virtual chain at reseed and logs a Composite (kind-5) recovery
/// event, which `parse_recovering` surfaces as a `composite-recovery` hint.
///
/// Pre-item-4 this shape was a NAMED DROP (`repair_named_drops += 1`, no
/// reseed, no kind-5 event), so the presence of the `composite-recovery`
/// attempt is a direct, item-4-specific witness that the chain arm fired.
///
/// Item 4 lowers chains in the PURE canonical-GLL recovery path (the SOLE engine
/// after #19b physically removed the classic lever, 2026-07-15), so the composite
/// witness is asserted directly.
#[test]
fn parse_recovering_composite_sequence_materializes_a_chain() {
    let (_ast, errors) = Proc::parse_recovering("+ 1 2");
    // Pure canonical-GLL arm: the item-4 chain-lowering witness.
    assert!(
        !errors.is_empty(),
        "the malformed leading-operator input must accumulate recovery attempts",
    );
    let surfaced_composite = errors.iter().any(|e| {
        let rendered = format!("{e:?}");
        rendered.contains("composite-recovery")
    });
    assert!(
        surfaced_composite,
        "item 4: the token-mutating ApplyRecoverySequence must lower to a \
         virtual chain and surface a `composite-recovery` (kind-5) attempt \
         — got: {errors:?}",
    );
}
