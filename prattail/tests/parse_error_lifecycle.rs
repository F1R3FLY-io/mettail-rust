use mettail_prattail::runtime_types::{ParseError, Position, Range};
use mettail_prattail::wpda_runtime::{
    ActionInvocationError, RealizationError, ReconstructionFailure,
};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn range() -> Range {
    Range {
        start: Position::zero(),
        end: Position::zero(),
        file_id: None,
    }
}

#[test]
fn parse_error_lifecycle_and_formatting_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("parse-error-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut error = ParseError::LexError {
                message: "bad token".to_string(),
                position: Position::zero(),
            };
            for _ in 0..DEPTH {
                error = ParseError::RecoveryApplied {
                    original_error: Box::new(error),
                    repair_description: "skip".to_string(),
                    range: range(),
                };
            }

            let cloned = error.clone();
            assert_eq!(error.range(), range());
            let display = error.to_string();
            assert!(display.starts_with("1:1: bad token"));
            assert!(display.ends_with("(recovered: skip)"));
            assert_eq!(display.matches("(recovered: skip)").count(), DEPTH);
            let debug = format!("{error:?}");
            assert!(debug.starts_with("RecoveryApplied { original_error: RecoveryApplied"));
            assert!(debug.contains("LexError { message: \"bad token\""));

            drop(cloned);
            drop(error);
        })
        .expect("spawn parse-error small-stack gate")
        .join()
        .expect("parse-error small-stack gate panicked");
}

#[test]
fn parse_error_formatting_preserves_compact_contracts() {
    let error = ParseError::RecoveryApplied {
        original_error: Box::new(ParseError::UnexpectedEof {
            expected: "term".into(),
            range: range(),
            hint: Some("add a term".into()),
        }),
        repair_description: "inserted placeholder".to_string(),
        range: range(),
    };
    assert_eq!(
        error.to_string(),
        "1:1: unexpected end of input, expected term\n  = hint: add a term (recovered: inserted placeholder)"
    );
    assert_eq!(
        format!("{error:?}"),
        "RecoveryApplied { original_error: UnexpectedEof { expected: \"term\", range: Range { start: Position { byte_offset: 0, line: 0, column: 0 }, end: Position { byte_offset: 0, line: 0, column: 0 }, file_id: None }, hint: Some(\"add a term\") }, repair_description: \"inserted placeholder\", range: Range { start: Position { byte_offset: 0, line: 0, column: 0 }, end: Position { byte_offset: 0, line: 0, column: 0 }, file_id: None } }"
    );
}

#[test]
fn realization_failure_remains_distinct_from_invalid_syntax() {
    let error = ParseError::RealizationFailed {
        error: mettail_semantic_key::ContentKeyCacheError::ResourceExhausted {
            limit: 8,
            requested: 9,
        }
        .into(),
        range: range(),
    };

    assert_eq!(error.range(), range());
    assert_eq!(
        error.to_string(),
        "1:1: parser realization failed: semantic-key cache entry limit 8 exceeded (requested 9)"
    );
    assert!(matches!(
        error.clone(),
        ParseError::RealizationFailed {
            error: mettail_prattail::wpda_runtime::RealizationError::SemanticKey(
                mettail_semantic_key::ContentKeyCacheError::ResourceExhausted {
                    limit: 8,
                    requested: 9,
                }
            ),
            ..
        }
    ));
}

#[test]
fn realization_failure_preserves_reconstruction_and_resource_causes() {
    let cases = [
        (RealizationError::Reconstruction { node: 7, cause: ReconstructionFailure::TraversalLimit { limit: 32 } },
            "1:1: parser realization failed: reconstruction at forest node 7 failed: occurrence traversal exceeded its work limit 32"),
        (RealizationError::Action { rule_idx: 3, cause: ActionInvocationError::CollectionLimit { limit: 256, actual: 257 } },
            "1:1: parser realization failed: reconstruction action for rule 0x3 failed: action collection limit 256 exceeded (requested 257)"),
        (RealizationError::Action { rule_idx: 3, cause: ActionInvocationError::RepeatedCollectionDrain { id: 0 } },
            "1:1: parser realization failed: reconstruction action for rule 0x3 failed: action collection slot 0 was drained more than once"),
    ];
    for (cause, expected) in cases {
        let error = ParseError::RealizationFailed { error: cause.clone(), range: range() };
        assert_eq!(error.to_string(), expected);
        assert_eq!(error.range(), range());
        match error.clone() {
            ParseError::RealizationFailed { error: ref retained, .. } => {
                assert_eq!(retained, &cause)
            },
            other => panic!("realization failure changed kind: {other:?}"),
        }
        assert!(std::error::Error::source(&cause).is_some());
    }
}
