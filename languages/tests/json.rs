//! GSLT omnibus conformance suite for **L1 `Json`** — the hand-written gate on
//! the production spec `languages/src/json.rs` (`omnibus.tex:393-415`), rung one
//! (types + terms only; `equations { }` and `rewrites { }` are empty).
//!
//! The spec's own module header carries the clause-by-clause containment table,
//! the notation notes, and the ★ documented delta on how `List(X)` is carried;
//! this file carries the behaviour those clauses claim. Rung one's whole content
//! is the SURFACE, so every conformance statement here is a parse plus a display
//! round-trip — `parse(display(t)) == t` is the real gate.
#![cfg(feature = "json")]

use mettail_languages::json::*;
use mettail_runtime::Language;

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests — every clause of `languages/src/json.rs` is exercised by a parse.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn json_language_resolves() {
    let lang = JsonLanguage;
    assert_eq!(lang.name(), "Json");
}

/// Clause coverage: the metadata carries all seven `terms` productions.
#[test]
fn json_metadata_carries_every_doc_clause() {
    let lang = JsonLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["JNull", "JBool", "JNum", "JStr", "JArr", "JObj", "Field"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    // Rung one: the theory declares no dynamics. `equations()` is exactly empty;
    // `rewrites()` carries ONLY macro-synthesized numeric-cast adapters derived
    // from the native carriers (`Bool` ⊑ `BigRat` lossless coercion — see
    // `docs/design/made/native-types/numeric-cast-adapter-generation.md`), never a
    // user-declared rule.
    assert!(meta.equations().is_empty(), "Json is rung one — `equations {{ }}` is empty");
    for rw in meta.rewrites() {
        let name = rw.name.unwrap_or("<unnamed>");
        assert!(
            name.ends_with("Cong") || name.starts_with("Norm"),
            "Json declares no rewrites; every entry must be a macro-synthesized cast \
             adapter, found {name:?} in {:?}",
            meta.rewrites().iter().map(|r| r.name).collect::<Vec<_>>()
        );
    }
}

/// `JNull` (:403).
#[test]
fn json_parses_null() {
    mettail_runtime::clear_var_cache();
    let t = Value::parse("null").expect("JNull parse");
    assert_eq!(format!("{t}"), "null");
}

/// `JBool` (:404).
#[test]
fn json_parses_booleans() {
    mettail_runtime::clear_var_cache();
    for src in ["true", "false"] {
        let t = Value::parse(src).unwrap_or_else(|e| panic!("JBool parse of {src:?}: {e:?}"));
        assert_eq!(format!("{t}"), src);
    }
}

/// `JNum` (:405) — exact rational reading of a JSON number.
#[test]
fn json_parses_numbers_exactly() {
    mettail_runtime::clear_var_cache();
    let t = Value::parse("42").expect("JNum integer parse");
    assert!(!format!("{t}").is_empty());
    let t = Value::parse("3.14").expect("JNum decimal parse");
    // 3.14 is EXACTLY 157/50 in the rational carrier.
    let shown = format!("{t}");
    assert!(
        shown.contains("157") || shown.contains("3.14"),
        "decimal must be read exactly (157/50), got {shown:?}"
    );
}

/// `JStr` (:406).
#[test]
fn json_parses_strings() {
    mettail_runtime::clear_var_cache();
    let t = Value::parse("\"hello\"").expect("JStr parse");
    assert_eq!(format!("{t}"), "\"hello\"");
}

#[test]
fn json_string_escape_pairs_decode_left_to_right_and_round_trip() {
    mettail_runtime::clear_var_cache();
    let raw = r#""a\\\"b\\\\c""#;
    let value = Value::parse(raw).expect("JStr overlapping escape-pair parse");
    assert_eq!(value.to_string(), raw);
    assert_eq!(Value::parse(&value.to_string()).expect("JStr display reparses"), value);
}

/// `JArr` (:407) — the `List(Value)` → `Vec(Value)` clause.
#[test]
fn json_parses_arrays() {
    mettail_runtime::clear_var_cache();
    let t = Value::parse("[null,true,\"x\"]").expect("JArr parse");
    let shown = format!("{t}");
    assert!(shown.starts_with('['), "array must render bracketed, got {shown:?}");
    assert!(
        shown.contains("null") && shown.contains("true"),
        "elements preserved: {shown:?}"
    );
}

/// `JObj` (:408) + `Field` (:409).
#[test]
fn json_parses_objects_with_fields() {
    mettail_runtime::clear_var_cache();
    let t = Value::parse("{\"a\":1,\"b\":null}").expect("JObj parse");
    let shown = format!("{t}");
    assert!(shown.contains("\"a\""), "field key preserved: {shown:?}");
    assert!(shown.contains("null"), "field value preserved: {shown:?}");
}

/// The composite document: every production in one term, plus a display
/// round-trip (parse(display(t)) == t), which is the real conformance gate.
#[test]
fn json_whole_document_round_trips() {
    mettail_runtime::clear_var_cache();
    let src = "{\"name\":\"gslt\",\"ok\":true,\"n\":3.14,\"tags\":[\"a\",\"b\"],\"nil\":null}";
    let t = Value::parse(src).unwrap_or_else(|e| panic!("whole-document parse failed: {e:?}"));
    let printed = format!("{t}");
    let reparsed = Value::parse(&printed)
        .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
    assert_eq!(reparsed, t, "display round-trip must be identity (printed {printed:?})");
}

/// Display round-trip across every shape the grammar admits — nullary, each
/// literal carrier, and all three arity cases of both collections.
#[test]
fn json_every_shape_round_trips() {
    for src in [
        "null",
        "true",
        "false",
        "42",
        "-7",
        "3.14",
        "\"hi\"",
        "[]",
        "[1]",
        "[1,2]",
        "[1,2,3]",
        "{}",
        "{\"a\":1}",
        "{\"a\":1,\"b\":2}",
        "{\"a\":[1,2],\"b\":null}",
    ] {
        mettail_runtime::clear_var_cache();
        let t = Value::parse(src).unwrap_or_else(|e| panic!("parse of {src:?} failed: {e:?}"));
        let printed = format!("{t}");
        let reparsed = Value::parse(&printed).unwrap_or_else(|e| {
            panic!("re-parse of display {printed:?} (from {src:?}) failed: {e:?}")
        });
        assert_eq!(reparsed, t, "round-trip identity failed for {src:?} (printed {printed:?})");
    }
}
