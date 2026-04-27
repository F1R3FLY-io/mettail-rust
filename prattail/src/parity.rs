//! Parity testing infrastructure (Model B golden ASTs via postcard).
//!
//! Stage 8 of W7 plan v5.1. Provides serialization helpers for capturing
//! parser output as binary postcard files (`.golden.bin`), comparing live
//! output against goldens, and rendering human-readable diffs on mismatch.
//!
//! ## Why postcard?
//!
//! The user feedback (saved at `feedback_postcard_over_serde_json.md`)
//! mandates postcard for all serialization in this project: serde_json
//! has macOS issues. Postcard reuses serde derives, so any AST that
//! already implements `Serialize`/`Deserialize` works without changes.
//!
//! ## Two parity models
//!
//! - **Model A (dual codegen)**: macros emit BOTH the legacy trampoline
//!   parser and the new WPDS engine. Tests parse the same input through
//!   both and assert byte-equality. Requires Stage 6 codegen feature
//!   parity; tracked in [`mod model_a`].
//! - **Model B (golden ASTs)**: parse known inputs with the authoritative
//!   parser, postcard-encode the AST, store as `.golden.bin`. Replay tests
//!   decode and compare. Stable across parser changes that preserve AST
//!   structure. Implemented here.
//!
//! ## Workflow
//!
//! ```ignore
//! use mettail_prattail::parity;
//!
//! // Capture: parse input, encode AST, write to .golden.bin
//! let ast = my_language::parse_Expr("1 + 2 * 3").unwrap();
//! parity::write_golden("target/goldens/expr_basic.golden.bin", &ast)?;
//!
//! // Replay: read .golden.bin, decode, compare against fresh parse
//! let actual = my_language::parse_Expr("1 + 2 * 3").unwrap();
//! parity::assert_matches_golden("target/goldens/expr_basic.golden.bin", &actual)?;
//! ```

use std::path::Path;

use serde::{de::DeserializeOwned, Serialize};

// ══════════════════════════════════════════════════════════════════════════════
// Errors
// ══════════════════════════════════════════════════════════════════════════════

/// Errors emitted by the parity helpers.
#[derive(Debug)]
pub enum ParityError {
    /// I/O error while reading/writing a golden file.
    Io(std::io::Error),
    /// Postcard encoding failure.
    Encode(postcard::Error),
    /// Postcard decoding failure (golden corrupted or schema drift).
    Decode(postcard::Error),
    /// Live output did not match the stored golden. Carries a rendered diff.
    Mismatch { rendered_diff: String },
}

impl std::fmt::Display for ParityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParityError::Io(e) => write!(f, "parity I/O error: {}", e),
            ParityError::Encode(e) => write!(f, "parity encode error: {}", e),
            ParityError::Decode(e) => write!(f, "parity decode error: {}", e),
            ParityError::Mismatch { rendered_diff } => {
                write!(f, "parity mismatch:\n{}", rendered_diff)
            }
        }
    }
}

impl std::error::Error for ParityError {}

impl From<std::io::Error> for ParityError {
    fn from(e: std::io::Error) -> Self {
        ParityError::Io(e)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Encode / decode
// ══════════════════════════════════════════════════════════════════════════════

/// Encode a value to postcard bytes.
///
/// Convenience wrapper around `postcard::to_allocvec` producing a `Vec<u8>`.
pub fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>, ParityError> {
    postcard::to_allocvec(value).map_err(ParityError::Encode)
}

/// Decode a value from postcard bytes.
pub fn decode<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, ParityError> {
    postcard::from_bytes(bytes).map_err(ParityError::Decode)
}

// ══════════════════════════════════════════════════════════════════════════════
// Golden file I/O
// ══════════════════════════════════════════════════════════════════════════════

/// Write a value to a `.golden.bin` file.
///
/// Creates parent directories if needed. Overwrites any existing file at
/// the path. Use to (re)generate goldens after a deliberate AST change;
/// CI tests should NOT call this — they should call [`assert_matches_golden`].
pub fn write_golden<T: Serialize, P: AsRef<Path>>(
    path: P,
    value: &T,
) -> Result<(), ParityError> {
    let bytes = encode(value)?;
    if let Some(parent) = path.as_ref().parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(path, bytes).map_err(Into::into)
}

/// Read a value from a `.golden.bin` file.
pub fn read_golden<T: DeserializeOwned, P: AsRef<Path>>(path: P) -> Result<T, ParityError> {
    let bytes = std::fs::read(path)?;
    decode(&bytes)
}

// ══════════════════════════════════════════════════════════════════════════════
// Comparison and diff rendering
// ══════════════════════════════════════════════════════════════════════════════

/// Compare a live value against the golden stored at `path`.
///
/// On mismatch returns [`ParityError::Mismatch`] containing a
/// `format!("{:#?}", ...)`-rendered diff of expected vs actual values
/// (since postcard binaries are not human-readable, we Debug-render the
/// decoded values to give the test author actionable output).
///
/// On absent golden file returns [`ParityError::Io`] — typically the test
/// author should call [`write_golden`] once to seed.
pub fn assert_matches_golden<T, P>(path: P, actual: &T) -> Result<(), ParityError>
where
    T: Serialize + DeserializeOwned + std::fmt::Debug + PartialEq,
    P: AsRef<Path>,
{
    let actual_bytes = encode(actual)?;
    let golden_bytes = std::fs::read(path.as_ref())?;
    if actual_bytes == golden_bytes {
        return Ok(());
    }
    // Bytes differ — decode both and render a Debug-diff.
    let expected: T = decode(&golden_bytes)?;
    let rendered = render_debug_diff(&expected, actual);
    Err(ParityError::Mismatch { rendered_diff: rendered })
}

/// Render two values as `format!("{:#?}", _)` strings and produce a unified
/// human-readable diff suitable for inclusion in test failure messages.
///
/// Lightweight implementation: line-by-line side-by-side with a `>` / `<`
/// gutter. Sufficient for AST-shaped output; consumers wanting prettier
/// diffs can decode goldens via [`read_golden`] and use any external
/// diffing tool.
pub fn render_debug_diff<T: std::fmt::Debug>(expected: &T, actual: &T) -> String {
    let exp = format!("{:#?}", expected);
    let act = format!("{:#?}", actual);
    let exp_lines: Vec<&str> = exp.lines().collect();
    let act_lines: Vec<&str> = act.lines().collect();
    let max = exp_lines.len().max(act_lines.len());
    let mut out = String::new();
    out.push_str("--- expected (golden)\n");
    out.push_str("+++ actual\n");
    for i in 0..max {
        let e = exp_lines.get(i).copied().unwrap_or("");
        let a = act_lines.get(i).copied().unwrap_or("");
        if e == a {
            out.push_str("  ");
            out.push_str(e);
            out.push('\n');
        } else {
            if !e.is_empty() {
                out.push_str("- ");
                out.push_str(e);
                out.push('\n');
            }
            if !a.is_empty() {
                out.push_str("+ ");
                out.push_str(a);
                out.push('\n');
            }
        }
    }
    out
}

// ══════════════════════════════════════════════════════════════════════════════
// Model A — dual-codegen parity testing (Stage 6 Phase A.1 real impl)
// ══════════════════════════════════════════════════════════════════════════════

/// Dual-codegen parity testing.
///
/// Runs both parsers (legacy trampoline and new WPDS backend) against the
/// same input and asserts byte/structural/display equality via a
/// three-tier check:
///
/// 1. `PartialEq` — fastest; catches structural differences.
/// 2. Postcard byte-equal — catches serialization-relevant drift
///    (e.g., custom `PartialEq` impls that ignore fields like spans).
/// 3. `Display` roundtrip — catches AST shapes that render differently.
pub mod model_a {
    use super::{encode, render_debug_diff, ParityError};
    use serde::de::DeserializeOwned;
    use serde::Serialize;
    use std::fmt::{Debug, Display};

    /// Drive both parsers against `input` and assert three-tier parity.
    ///
    /// Returns `Ok(())` on full parity, `ParityError` on any tier failing.
    pub fn assert_dual_parses_eq<T, F1, F2, E1, E2>(
        input: &str,
        parse_legacy: F1,
        parse_wpds: F2,
    ) -> Result<(), ParityError>
    where
        T: Serialize + DeserializeOwned + Debug + PartialEq + Display,
        F1: Fn(&str) -> Result<T, E1>,
        F2: Fn(&str) -> Result<T, E2>,
        E1: Debug,
        E2: Debug,
    {
        let legacy = parse_legacy(input).map_err(|e| ParityError::Mismatch {
            rendered_diff: format!("legacy parser failed on {:?}: {:?}", input, e),
        })?;
        let wpds = parse_wpds(input).map_err(|e| ParityError::Mismatch {
            rendered_diff: format!("WPDS parser failed on {:?}: {:?}", input, e),
        })?;

        // Tier 1: PartialEq.
        if legacy != wpds {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 1: PartialEq] parse mismatch on input {:?}\n{}",
                    input,
                    render_debug_diff(&legacy, &wpds),
                ),
            });
        }

        // Tier 2: Postcard byte-equal.
        let legacy_bytes = encode(&legacy)?;
        let wpds_bytes = encode(&wpds)?;
        if legacy_bytes != wpds_bytes {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 2: postcard bytes] serialization mismatch on input {:?}\n\
                     legacy: {} bytes\nwpds:   {} bytes\n{}",
                    input,
                    legacy_bytes.len(),
                    wpds_bytes.len(),
                    render_debug_diff(&legacy, &wpds),
                ),
            });
        }

        // Tier 3: Display roundtrip.
        let legacy_display = format!("{}", legacy);
        let wpds_display = format!("{}", wpds);
        if legacy_display != wpds_display {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 3: Display] roundtrip mismatch on input {:?}\n\
                     legacy: {}\nwpds:   {}",
                    input, legacy_display, wpds_display,
                ),
            });
        }

        Ok(())
    }

    /// Convenience: assert parity on already-parsed values (without
    /// re-running the parsers). Useful when the tests have the values
    /// in hand and want the three-tier diff-on-mismatch reporting.
    pub fn assert_dual_parses_eq_values<T>(legacy: &T, wpds: &T) -> Result<(), ParityError>
    where
        T: Serialize + DeserializeOwned + Debug + PartialEq + Display,
    {
        if legacy != wpds {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 1: PartialEq] value mismatch\n{}",
                    render_debug_diff(legacy, wpds),
                ),
            });
        }
        let lb = encode(legacy)?;
        let wb = encode(wpds)?;
        if lb != wb {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 2: postcard bytes] value serialization mismatch: {} vs {} bytes",
                    lb.len(),
                    wb.len(),
                ),
            });
        }
        let ld = format!("{}", legacy);
        let wd = format!("{}", wpds);
        if ld != wd {
            return Err(ParityError::Mismatch {
                rendered_diff: format!(
                    "[Tier 3: Display] value roundtrip mismatch\nlegacy: {}\nwpds:   {}",
                    ld, wd,
                ),
            });
        }
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use serde::{Deserialize, Serialize};

        #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
        struct ToyAst {
            label: String,
            n: u32,
        }

        impl std::fmt::Display for ToyAst {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", self.label, self.n)
            }
        }

        fn good_legacy(_s: &str) -> Result<ToyAst, String> {
            Ok(ToyAst { label: "X".into(), n: 1 })
        }
        fn good_wpds(_s: &str) -> Result<ToyAst, String> {
            Ok(ToyAst { label: "X".into(), n: 1 })
        }
        fn drift_wpds(_s: &str) -> Result<ToyAst, String> {
            Ok(ToyAst { label: "X".into(), n: 2 })
        }

        #[test]
        fn parity_passes_on_matching_parses() {
            assert_dual_parses_eq("input", good_legacy, good_wpds).expect("match");
        }

        #[test]
        fn parity_fails_with_debug_diff_on_drift() {
            let r = assert_dual_parses_eq("input", good_legacy, drift_wpds);
            match r {
                Err(ParityError::Mismatch { rendered_diff }) => {
                    assert!(rendered_diff.contains("Tier 1"));
                    assert!(rendered_diff.contains("PartialEq"));
                }
                other => panic!("expected Mismatch, got {:?}", other),
            }
        }

        #[test]
        fn parity_value_variant_covers_three_tiers() {
            let a = ToyAst { label: "X".into(), n: 1 };
            let b = ToyAst { label: "X".into(), n: 1 };
            assert!(assert_dual_parses_eq_values(&a, &b).is_ok());
        }

        #[test]
        fn parity_value_variant_fails_cleanly_on_mismatch() {
            let a = ToyAst { label: "X".into(), n: 1 };
            let b = ToyAst { label: "X".into(), n: 2 };
            assert!(assert_dual_parses_eq_values(&a, &b).is_err());
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    struct ToyAst {
        label: String,
        children: Vec<ToyAst>,
    }

    fn ast(label: &str, children: Vec<ToyAst>) -> ToyAst {
        ToyAst {
            label: label.to_string(),
            children,
        }
    }

    #[test]
    fn encode_decode_round_trip() {
        let value = ast("Add", vec![ast("Lit", vec![]), ast("Lit", vec![])]);
        let bytes = encode(&value).expect("encode ok");
        let decoded: ToyAst = decode(&bytes).expect("decode ok");
        assert_eq!(value, decoded);
    }

    #[test]
    fn write_and_read_golden() {
        let dir = std::env::temp_dir().join("mettail_parity_tests");
        std::fs::create_dir_all(&dir).expect("create dir");
        let path = dir.join("write_and_read_golden.golden.bin");
        let value = ast("X", vec![ast("Y", vec![]), ast("Z", vec![])]);
        write_golden(&path, &value).expect("write ok");
        let read: ToyAst = read_golden(&path).expect("read ok");
        assert_eq!(value, read);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn assert_matches_golden_passes_when_equal() {
        let dir = std::env::temp_dir().join("mettail_parity_tests");
        std::fs::create_dir_all(&dir).expect("create dir");
        let path = dir.join("assert_matches_passes.golden.bin");
        let value = ast("Mul", vec![]);
        write_golden(&path, &value).expect("write ok");
        assert_matches_golden(&path, &value).expect("matches");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn assert_matches_golden_fails_with_diff_on_mismatch() {
        let dir = std::env::temp_dir().join("mettail_parity_tests");
        std::fs::create_dir_all(&dir).expect("create dir");
        let path = dir.join("assert_matches_fails.golden.bin");
        let golden = ast("Add", vec![ast("Lit_1", vec![])]);
        let actual = ast("Add", vec![ast("Lit_2", vec![])]);
        write_golden(&path, &golden).expect("write ok");
        let result = assert_matches_golden(&path, &actual);
        match result {
            Err(ParityError::Mismatch { rendered_diff }) => {
                assert!(rendered_diff.contains("expected (golden)"));
                assert!(rendered_diff.contains("actual"));
                // The diff should contain both Lit values.
                assert!(rendered_diff.contains("Lit_1"));
                assert!(rendered_diff.contains("Lit_2"));
            }
            other => panic!("expected Mismatch, got {:?}", other),
        }
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn assert_matches_golden_returns_io_error_for_missing_file() {
        let bogus_path = "/tmp/__definitely_does_not_exist_2026__/x.golden.bin";
        let actual = ast("X", vec![]);
        let r = assert_matches_golden(bogus_path, &actual);
        assert!(matches!(r, Err(ParityError::Io(_))));
    }

    #[test]
    fn render_debug_diff_marks_changed_lines() {
        let a = ast("Add", vec![ast("L", vec![])]);
        let b = ast("Sub", vec![ast("L", vec![])]);
        let d = render_debug_diff(&a, &b);
        assert!(d.contains("expected (golden)"));
        assert!(d.contains("actual"));
        // Different label appears in both '-' and '+' sides.
        assert!(d.contains("- "));
        assert!(d.contains("+ "));
    }

    #[test]
    fn render_debug_diff_handles_identical_values() {
        let a = ast("X", vec![]);
        let d = render_debug_diff(&a, &a);
        assert!(d.contains("expected (golden)"));
        // No - or + markers at the start of any non-header line.
        for line in d.lines() {
            if line.starts_with("---") || line.starts_with("+++") {
                continue;
            }
            assert!(!line.starts_with("- "), "no remove markers expected: {}", line);
            assert!(!line.starts_with("+ "), "no add markers expected: {}", line);
        }
    }

    #[test]
    fn write_golden_creates_parent_dirs() {
        let path = std::env::temp_dir()
            .join("mettail_parity_tests")
            .join("nested")
            .join("dirs")
            .join("test.golden.bin");
        // Make sure parent doesn't exist.
        let _ = std::fs::remove_dir_all(path.parent().unwrap().parent().unwrap());
        let value = ast("X", vec![]);
        write_golden(&path, &value).expect("write creates parents");
        assert!(path.exists());
        let _ = std::fs::remove_dir_all(
            std::env::temp_dir().join("mettail_parity_tests").join("nested"),
        );
    }

    #[test]
    fn parity_error_display_includes_kind() {
        let mismatch = ParityError::Mismatch {
            rendered_diff: "diff content".to_string(),
        };
        let s = format!("{}", mismatch);
        assert!(s.contains("parity mismatch"));
        assert!(s.contains("diff content"));
    }
}
