//! **The byte-array literal `b"deadbeef"` — its meaning, its round trip, and the ambiguity
//! it makes unspellable.**
//!
//! # What this pins, and why the pin had to exist before the carrier could land
//!
//! `Bytes` carries `Vec<u8>` (`![Vec<u8>] as Bytes`), which is upstream's model —
//! `RhoTypes.proto:230-232` has `string g_string = 3` and `bytes g_byte_array = 25` as TWO
//! DISTINCT wire carriers. The carrier change was implemented, measured, and HELD on 2026-07-29
//! (`2eebf722`) for one reason: it left `Bytes` with **no surface form at all**. A `Vec<u8>`
//! payload is not string-shaped, so no `StringLit` arm was emitted, and `Bytes` declares no
//! collection delimiters, so the collection `Display` arm wrapped its bytes in EMPTY open/close.
//! MEASURED then:
//!
//! ```text
//! gen_rholang_prop::bytes_display_parse_roundtrip
//!   arb_bytes produced unparseable surface term ""
//! ```
//!
//! A value constructible in Rust that the language can neither write nor print is a broken
//! `Display` → parse invariant for an entire category. `b"…"` is the missing surface.
//!
//! # The three questions this file answers
//!
//! | § | question | why it is not obvious |
//! |---|---|---|
//! | 1 | does `b"…"` denote the bytes it spells? | the digits are HEX pairs, not ASCII bytes — `b"deadbeef"` is 4 bytes, not 8 |
//! | 2 | is the `Str`/`Bytes` ambiguity now UNSPELLABLE? | it used to be *elected*; the fix is that no `"…"` token can inhabit `Bytes::BytesLit` |
//! | 3 | does every category that DECLARES a literal actually have a surface? | the held defect was a declared literal silently having none — the DERIVED gate for that lives in `rholang_literal_surface_census.rs`, and §3 explains why it is a separate binary |
//!
//! # Why HEX, and why it is a BUG FIX rather than a divergence
//!
//! Upstream ALREADY prints a byte array as bare hex —
//! `f1r3node-rust-mettail/rholang/src/rust/interpreter/pretty_printer.rs:2860`,
//! `GByteArray(bs) => Ok(hex::encode(bs))` — and upstream's own grammar cannot read that back
//! (`rholang-tree-sitter/grammar.js:435-436` offers `string_literal` and `uri_literal` only;
//! `ByteArray` at `:424` is a TYPE NAME in `simple_type`). Upstream therefore prints a value its
//! own parser rejects, and `par_to_sexpr.rs:107` spells the same value a *third* way (`0x…`).
//! `b"…"` frames exactly upstream's hex digits in something the parser accepts, so the digits
//! agree byte for byte and the round-trip upstream loses is recovered. Upstream is a floor on
//! semantics, not a ceiling on diagnostics; an upstream bug is a BUG FIX, never a DIVERGENCE.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{Bytes, Proc};

/// Lowercase hex, two digits per byte — the reference encoder this file measures `Display`
/// against. Deliberately written independently of the emitted one (`macros/src/gen/syntax/
/// display.rs`, the `is_byte_vector` arm) so that agreement is evidence rather than tautology.
fn reference_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// Every realized reading of `src`, ambiguity-preserving (no election).
fn all_readings(src: &str) -> Vec<Proc> {
    mettail_runtime::clear_var_cache();
    Proc::parse_via_wpda_all_with_weights(src)
        .unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
        .0
}

/// The byte payload of a `Proc` that is a ground byte array, or `None`.
fn byte_payload(term: &Proc) -> Option<Vec<u8>> {
    match term {
        Proc::CastBytes(inner) => match inner.as_ref() {
            Bytes::BytesLit(bytes) => Some(bytes.clone()),
            _ => None,
        },
        _ => None,
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════
// § 1 — the literal denotes the bytes it spells
// ════════════════════════════════════════════════════════════════════════════════════════

/// `b"deadbeef"` is FOUR bytes, `DE AD BE EF` — the hex-dump joke read as hex, which is what
/// upstream's `hex::encode` / `hexToBytes` pair means by those digits. Read as ASCII it would be
/// eight bytes; that reading is what this row excludes.
#[test]
fn a_byte_literal_names_the_bytes_it_spells() {
    let term = parse(r#"b"deadbeef""#);
    assert_eq!(
        byte_payload(&term),
        Some(vec![0xde, 0xad, 0xbe, 0xef]),
        "`b\"deadbeef\"` must be the four bytes DE AD BE EF (hex pairs), not the eight ASCII \
         bytes of the word; got {term:?}",
    );
}

/// `b""` is the EMPTY byte array, and it is in the language deliberately: it is what
/// `Bytes::BytesLit(vec![])` renders as, and the unrenderability of exactly that value — it came
/// out as the empty string under the collection `Display` arm's empty delimiters — was the
/// measured blocker recorded in `2eebf722`.
#[test]
fn the_empty_byte_array_has_a_surface() {
    let term = parse(r#"b"""#);
    assert_eq!(byte_payload(&term), Some(Vec::new()), "`b\"\"` must be the empty byte array");
    assert_eq!(
        format!("{term}"),
        r#"b"""#,
        "the empty byte array must RENDER as `b\"\"` — rendering it as the empty string is the \
         defect this row exists for",
    );
}

/// `Display` writes upstream's digits, and the word it writes parses back to the same bytes.
/// The table spans the cases that break naive encoders: empty, a single byte needing a leading
/// zero, `0x00`, `0xff`, and a non-UTF-8 sequence that the retired `String` carrier could not
/// have held at all.
#[test]
fn display_writes_upstream_hex_and_the_word_parses_back() {
    let corpus: &[&[u8]] = &[
        &[],
        &[0x00],
        &[0x0f],
        &[0xff],
        &[0xde, 0xad, 0xbe, 0xef],
        &[0x00, 0x01, 0x02, 0x03, 0x04],
        // Not valid UTF-8 (a lone continuation byte and a bare lead byte): unrepresentable
        // under the retired `![String] as Bytes` carrier, which is the point.
        &[0x80, 0xc3, 0x28, 0xfe],
    ];
    for bytes in corpus {
        let term = Proc::CastBytes(std::sync::Arc::new(Bytes::BytesLit(bytes.to_vec())));
        let rendered = format!("{term}");
        assert_eq!(
            rendered,
            format!("b\"{}\"", reference_hex(bytes)),
            "Display must write `b\"<lowercase hex>\"` for {bytes:02x?}",
        );
        assert_eq!(
            byte_payload(&parse(&rendered)),
            Some(bytes.to_vec()),
            "`{rendered}` must parse back to {bytes:02x?} — Display → parse is a real invariant \
             of the language, not a test convenience",
        );
    }
}

/// Both hex cases are ACCEPTED and lowercase is WRITTEN, so canonical idempotence holds after one
/// round. Upstream's `hexToBytes` (`reduce.rs:4849`) is likewise case-insensitive, so accepting
/// uppercase is alignment rather than licence.
#[test]
fn uppercase_hex_is_accepted_and_normalises_to_lowercase() {
    let upper = parse(r#"b"DEADBEEF""#);
    assert_eq!(
        byte_payload(&upper),
        Some(vec![0xde, 0xad, 0xbe, 0xef]),
        "uppercase hex digits must name the same bytes as lowercase ones",
    );
    assert_eq!(
        format!("{upper}"),
        r#"b"deadbeef""#,
        "Display must normalise to lowercase, matching upstream's `hex::encode`",
    );
    assert_eq!(
        format!("{}", parse(&format!("{upper}"))),
        format!("{upper}"),
        "and the lowercase word must be a FIXPOINT of parse ∘ display",
    );
}

/// An ODD number of hex digits names no byte sequence, and the REGEX excludes it (pairs:
/// `([0-9A-Fa-f][0-9A-Fa-f])*`) rather than the `eval` body rejecting it afterwards. So there is
/// no byte-array reading of `b"abc"`; the surface is not a byte array at all.
#[test]
fn an_odd_digit_count_is_not_a_byte_array() {
    mettail_runtime::clear_var_cache();
    let readings = Proc::parse_via_wpda_all_with_weights(r#"b"abc""#)
        .map(|(terms, _)| terms)
        .unwrap_or_default();
    assert!(
        readings.iter().all(|t| byte_payload(t).is_none()),
        "`b\"abc\"` has an odd digit count and must have NO byte-array reading; got {readings:?}",
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════
// § 2 — the `Str` / `Bytes` ambiguity is UNSPELLABLE, not elected
// ════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE AMBIGUITY IS GONE AT THE DECLARATION. Under `![String] as Bytes` both categories were
/// string-shaped, so the generator emitted a `StringLit` variant for each and every `"…"` in the
/// language had two readings — cohort 9 of `rholang_semantic_predicate_ambiguity`,
/// `[StringLit] CastStr vs CastBytes`. With a `Vec<u8>` payload no `"…"` token can inhabit
/// `Bytes`, so the reading is not *deprioritised*, it is unconstructible.
#[test]
fn a_string_literal_has_no_byte_array_reading() {
    let readings = all_readings(r#""deadbeef""#);
    assert!(!readings.is_empty(), "the control: a string literal must still parse",);
    assert!(
        readings.iter().all(|t| matches!(t, Proc::CastStr(_))),
        "every reading of a `\"…\"` literal must be a `CastStr`; a `CastBytes` reading means the \
         `Bytes` carrier is string-shaped again. Got {readings:?}",
    );
}

/// The positive control for the lexer fork: `b` is an ordinary identifier everywhere it is not
/// abutted to a `"`. Rholang has no juxtaposition, so `b"…"` was not a term in the language
/// before this literal existed — which is why no existing program changes meaning.
#[test]
fn an_identifier_named_b_is_unaffected() {
    let term = parse("for (b <- ch) { b }");
    assert!(
        !format!("{term}").contains("b\""),
        "a receive binding the name `b` must not acquire a byte-literal reading: {term}",
    );
    // And the abutted form IS the literal, so the two are distinguished by adjacency alone.
    assert_eq!(byte_payload(&parse(r#"b"00""#)), Some(vec![0x00]));
}

// ════════════════════════════════════════════════════════════════════════════════════════
// § 3 — the surface census lives NEXT DOOR, deliberately
// ════════════════════════════════════════════════════════════════════════════════════════
//
// The general gate — *every category that declares a `literals { … }` block must have a
// reachable surface*, with its domain derived from the grammar and floored against vacuity —
// is `languages/tests/rholang_literal_surface_census.rs`.
//
// ★ WHY IT IS A SEPARATE BINARY. This file names `Bytes::BytesLit`, so against a tree where the
// carrier has been reverted it does not COMPILE — decisive evidence that the variant is absent,
// but it tells us nothing about whether the census gate itself would fire. The census file
// references no category-specific variant, so it compiles against the reverted tree and fails
// with its own diagnostic instead. Both REDs were measured on 2026-07-30 and are quoted in the
// landing commit message.
