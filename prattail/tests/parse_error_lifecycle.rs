use mettail_prattail::runtime_types::{ParseError, Position, Range};

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
