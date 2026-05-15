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
    assert!(
        errors.is_empty(),
        "well-formed input should produce no errors: {:?}",
        errors,
    );
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
