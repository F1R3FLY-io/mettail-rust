//! **The byte-array METHODS, and the derived table of what upstream offers.**
//!
//! # Why this file exists, and why it exists NOW
//!
//! Before `b"…"` (`713e0364`) a `Bytes` value had no surface, so nothing could be written that
//! applied a method to one and every gap in the method surface was **unreachable**. The literal
//! makes them reachable, so the gaps become real defects at exactly the moment the literal lands.
//! This file is the enumeration and the fix's pin.
//!
//! # THE DERIVED TABLE — upstream `method_table` entries with a `GByteArray` arm
//!
//! Derived by walking every `fn <name>_method` in
//! `f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs` and reporting the ones whose
//! body has a `GByteArray` arm (the table itself is built at `:9337-9405`):
//!
//! | # | method | signature at the byte carrier | site |
//! |---|---|---|---|
//! | 1 | `nth(i)` | `ByteArray × Int → Int` | `:4670` |
//! | 2 | `last()` | `ByteArray → Int` | `:4753` |
//! | 3 | `toByteArray()` | `term → ByteArray` | `:4815` |
//! | 4 | `hexToBytes()` | `String → ByteArray` | `:4849` |
//! | 5 | `bytesToHex()` | `ByteArray → String` | `:4893` |
//! | 6 | `toUtf8Bytes()` | `String → ByteArray` | `:4948` |
//! | 7 | `length()` | `ByteArray → Int` | `:8775` |
//! | 8 | `slice(from, until)` | `ByteArray × Int × Int → ByteArray` | `:8857` |
//!
//! ★ **THE COUNT DEPENDS ENTIRELY ON THE AXIS, and every previously-quoted figure was correct on
//! some axis and wrong on the one it was quoted for.** The register's own §7.6 finding 5 warns
//! about exactly this, so all four axes are recorded:
//!
//! | axis | domain | upstream | mettail had | mettail has now |
//! |---|---|---|---|---|
//! | **A** — `method_table` entries with a `GByteArray` arm | the 8 above | 8 | 4 declared by NAME | 7 declared by name |
//! | **B** — byte-NAMED methods | `toByteArray`, `hexToBytes`, `bytesToHex`, `toUtf8Bytes` | 4 | **1** (`toByteArray`) | **4** |
//! | **C** — byte-PRODUCING surface incl. crypto system processes | B ∪ `sha256Hash`, `keccak256Hash`, `blake2b256Hash`, `secp256k1Verify`, `ed25519Verify` | 9 | 1 | 4 (the five crypto builtins are channels, not methods, and remain absent) |
//! | **D** — methods that ACCEPT a `Bytes` RECEIVER in mettail's host fold lane | the 8 above | 8 | **0** | **3** (`length`, `nth`, `last`) |
//!
//! Axis B's `1 of 4` and axis C's `1 of 9` (the latter recorded in register entry CBR-L13) are
//! both right; they answer different questions. **Axis D is the one nobody had measured, and it is
//! the one that mattered**: even the four methods whose NAMES mettail declared had no `Bytes` arm
//! at all — `fold_proc_length` (`languages/src/rholang/runtime.rs`) matched
//! `CastStr`/`CastList`/`CastMap`/`CastBag`/`CastSet` and not `CastBytes`, and `LNth`/`LLast`
//! matched only `Proc::CastList`. So `b"dead".length()` folded to the `error` term while the
//! machine answered `2`: a **fold/machine disagreement**, newly reachable.
//!
//! # `slice` is DELIBERATELY still absent, and that is a different work item
//!
//! `slice` is missing for **every** carrier in mettail — `String`, `List` and `ByteArray` alike —
//! so its absence is not a byte gap; it is a missing method. Adding it means declaring one rule
//! with three carrier arms and reserving a new keyword for all categories, which is a change whose
//! blast radius has nothing to do with bytes. It is reported rather than smuggled in here.
//!
//! # ⚠ `hexToBytes` REPRODUCES AN UPSTREAM ODDITY ON PURPOSE
//!
//! Upstream's decoder is `StringOps::unsafe_decode_hex` (`models/src/rust/string_ops.rs:17-28`),
//! which **filters out every non-hex-digit character** and then **left-pads an odd-length result
//! with `0`**, explicitly matching Scala's `Base16.unsafeDecode`. So `"hello world".hexToBytes()`
//! is `[0xed]` — the `e` and the `d` survive the filter — and `"abc".hexToBytes()` is `[0x0a,
//! 0xbc]`. That is lossy and surprising, and it is **not** repaired here: `hexToBytes` is
//! consensus-reachable upstream (`Registry.rho` calls it on public keys), so changing the decoder
//! would change a COMPUTED VALUE on a live path. Upstream is a floor on semantics; a deliberate,
//! documented, consensus-load-bearing behaviour is not a bug to fix, and the rows below pin it so
//! nobody "cleans it up".

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{
    Bytes, Int, Proc, RholangLanguage, RholangTerm, RholangTermInner, Str,
};
use mettail_runtime::Language;

/// Generous bounds; every row here settles in a handful of steps.
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// Parse `src` and dovetail-normalize it — the HOST fold lane, which is the lane whose byte arms
/// were missing. (The machine lane is pinned separately in `rholang-runtime`'s conformance
/// suites; the point of these rows is that the two now agree instead of disagreeing.)
fn fold(src: &str) -> Proc {
    let term = RholangTerm(RholangTermInner::Proc(parse(src)));
    let normal = RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .unwrap_or_else(|e| panic!("`{src}` must dovetail-normalize: {e:?}"));
    match normal.as_any().downcast_ref::<RholangTerm>().map(|t| &t.0) {
        Some(RholangTermInner::Proc(p)) => p.clone(),
        other => panic!("`{src}` normalized to a non-`Proc` term: {other:?}"),
    }
}

fn as_int(term: &Proc) -> Option<i64> {
    match term {
        Proc::CastInt(inner) => match inner.as_ref() {
            Int::NumLit(n) => Some(*n),
            _ => None,
        },
        _ => None,
    }
}

fn as_bytes(term: &Proc) -> Option<Vec<u8>> {
    match term {
        Proc::CastBytes(inner) => match inner.as_ref() {
            Bytes::BytesLit(bytes) => Some(bytes.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn as_str(term: &Proc) -> Option<String> {
    match term {
        Proc::CastStr(inner) => match inner.as_ref() {
            Str::StringLit(text) => Some(text.clone()),
            _ => None,
        },
        _ => None,
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════
// AXIS D — the three methods whose names mettail already declared now accept a `Bytes`
// ════════════════════════════════════════════════════════════════════════════════════════

/// `length()` on a byte array is its BYTE COUNT — upstream `reduce.rs:8775`,
/// `GByteArray(bytes) => new_gint_expr(bytes.len())`. Two hex digits are one byte, so
/// `b"dead"` has length 2 and not 4.
#[test]
fn length_of_a_byte_array_is_its_byte_count() {
    assert_eq!(
        as_int(&fold(r#"b"dead".length()"#)),
        Some(2),
        "`b\"dead\".length()` must be 2 (bytes), not 4 (hex digits) and not the `error` term",
    );
    assert_eq!(as_int(&fold(r#"b"".length()"#)), Some(0), "the empty byte array has length 0");
    assert_eq!(as_int(&fold(r#"b"deadbeef".length()"#)), Some(4));
}

/// `nth(i)` on a byte array is the UNSIGNED byte value at `i`, as an integer — upstream
/// `reduce.rs:4670`, `new_gint_par(b as i64, …)`. `0xad` is 173, so the sign of the byte does not
/// leak: a byte ≥ 0x80 must not come back negative.
#[test]
fn nth_of_a_byte_array_is_the_unsigned_byte_value() {
    assert_eq!(as_int(&fold(r#"b"deadbeef".nth(0)"#)), Some(0xde));
    assert_eq!(as_int(&fold(r#"b"deadbeef".nth(1)"#)), Some(0xad));
    assert_eq!(as_int(&fold(r#"b"deadbeef".nth(3)"#)), Some(0xef));
    assert_eq!(
        as_int(&fold(r#"b"80".nth(0)"#)),
        Some(128),
        "0x80 must come back as 128, not -128 — upstream converts to UNSIGNED",
    );
    // Out of range is the `error` term, the same fail-closed answer every out-of-domain
    // collection access gives here (see the `LNth` note in `languages/src/rholang.rs`).
    assert!(
        matches!(fold(r#"b"dead".nth(9)"#), Proc::Err),
        "an out-of-range index must be the `error` term, never a panic and never a fabricated 0",
    );
}

/// `last()` on a byte array is `nth(len - 1)` reached through the same projection — upstream
/// `reduce.rs:4753` binds the index to `len.saturating_sub(1)` and then runs `nth`'s arm verbatim.
#[test]
fn last_of_a_byte_array_is_its_final_byte() {
    assert_eq!(as_int(&fold(r#"b"deadbeef".last()"#)), Some(0xef));
    assert_eq!(as_int(&fold(r#"b"ff".last()"#)), Some(255));
    // `b"".last()` is the `error` term for the same reason `[].last()` is: `saturating_sub`
    // yields 0, and 0 is not `< 0`, so the projection misses. Inherited, not chosen here.
    assert!(
        matches!(fold(r#"b"".last()"#), Proc::Err),
        "the empty byte array's `last()` must be the `error` term",
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════
// AXIS B — the three byte-NAMED methods mettail lacked
// ════════════════════════════════════════════════════════════════════════════════════════

/// `hexToBytes()` decodes a hex STRING to a byte array — upstream `reduce.rs:4849`.
#[test]
fn hex_to_bytes_decodes_a_hex_string() {
    assert_eq!(
        as_bytes(&fold(r#""deadbeef".hexToBytes()"#)),
        Some(vec![0xde, 0xad, 0xbe, 0xef]),
        "the canonical case: an even-length, all-hex string",
    );
    assert_eq!(as_bytes(&fold(r#""".hexToBytes()"#)), Some(Vec::new()));
    assert_eq!(
        as_bytes(&fold(r#""DEADBEEF".hexToBytes()"#)),
        Some(vec![0xde, 0xad, 0xbe, 0xef]),
        "upstream's decoder is case-insensitive (`is_ascii_hexdigit`)",
    );
}

/// ⚠ THE UPSTREAM ODDITY, PINNED SO IT IS NOT "CLEANED UP".
/// `StringOps::unsafe_decode_hex` (`models/src/rust/string_ops.rs:17-28`) FILTERS non-hex
/// characters and LEFT-PADS an odd-length result, explicitly matching Scala's
/// `Base16.unsafeDecode`. It is lossy and surprising, and it is consensus-reachable upstream
/// (`Registry.rho` calls `hexToBytes` on public keys), so reproducing it is required and
/// "improving" it would change a computed value on a live path.
#[test]
fn hex_to_bytes_filters_and_pads_exactly_as_upstream_does() {
    assert_eq!(
        as_bytes(&fold(r#""abc".hexToBytes()"#)),
        Some(vec![0x0a, 0xbc]),
        "an ODD digit count is LEFT-PADDED with a zero nibble: \"abc\" ⇒ \"0abc\" ⇒ [0x0a, 0xbc]",
    );
    assert_eq!(
        as_bytes(&fold(r#""de-ad".hexToBytes()"#)),
        Some(vec![0xde, 0xad]),
        "non-hex characters are FILTERED OUT, not rejected",
    );
    assert_eq!(
        as_bytes(&fold(r#""hello world".hexToBytes()"#)),
        Some(vec![0xed]),
        "the filter keeps only `e` and `d`, so this lossy answer IS upstream's answer",
    );
}

/// `bytesToHex()` renders a byte array as a lowercase hex STRING — upstream `reduce.rs:4893`,
/// `bytes.iter().map(|byte| format!("{:02x}", byte)).collect()`.
#[test]
fn bytes_to_hex_renders_lowercase_hex() {
    assert_eq!(as_str(&fold(r#"b"deadbeef".bytesToHex()"#)), Some("deadbeef".to_string()));
    assert_eq!(as_str(&fold(r#"b"".bytesToHex()"#)), Some(String::new()));
    assert_eq!(
        as_str(&fold(r#"b"000f".bytesToHex()"#)),
        Some("000f".to_string()),
        "each byte is TWO digits, so leading zeros are preserved",
    );
}

/// `hexToBytes` and `bytesToHex` are mutually inverse on the canonical spelling, which is also
/// the spelling `b"…"` and `Display` use — so the three surfaces agree on one set of digits.
#[test]
fn hex_to_bytes_and_bytes_to_hex_are_inverse_on_the_canonical_spelling() {
    for word in ["", "00", "0f", "ff", "deadbeef", "0001020304"] {
        let round = fold(&format!(r#""{word}".hexToBytes().bytesToHex()"#));
        assert_eq!(
            as_str(&round),
            Some(word.to_string()),
            "`\"{word}\".hexToBytes().bytesToHex()` must be `\"{word}\"`",
        );
        // And the byte-literal spelling of the same digits agrees.
        assert_eq!(
            as_bytes(&fold(&format!(r#""{word}".hexToBytes()"#))),
            as_bytes(&parse(&format!(r#"b"{word}""#))),
            "`\"{word}\".hexToBytes()` and `b\"{word}\"` must denote the SAME bytes",
        );
    }
}

/// `toUtf8Bytes()` is the UTF-8 encoding of a string — upstream `reduce.rs:4948`,
/// `utf8_string.as_bytes().to_vec()`. It is a DIFFERENT function from `hexToBytes`, and the pair
/// `"dead"` distinguishes them sharply: as hex it is 2 bytes, as UTF-8 it is 4.
#[test]
fn to_utf8_bytes_encodes_the_string_itself() {
    assert_eq!(
        as_bytes(&fold(r#""dead".toUtf8Bytes()"#)),
        Some(vec![b'd', b'e', b'a', b'd']),
        "`\"dead\".toUtf8Bytes()` is the four ASCII bytes of the word",
    );
    assert_eq!(
        as_bytes(&fold(r#""dead".hexToBytes()"#)),
        Some(vec![0xde, 0xad]),
        "…whereas `hexToBytes` on the same string is TWO bytes — the control that keeps the two \
         methods from being confused",
    );
    assert_eq!(as_bytes(&fold(r#""".toUtf8Bytes()"#)), Some(Vec::new()));
    assert_eq!(
        as_bytes(&fold(r#""λ".toUtf8Bytes()"#)),
        Some(vec![0xce, 0xbb]),
        "a non-ASCII scalar encodes to its multi-byte UTF-8 form",
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════
// Dispositions out of domain — fail closed, never fabricate
// ════════════════════════════════════════════════════════════════════════════════════════

/// Applying a byte method at the wrong carrier answers the `error` term. It must not fabricate a
/// value, and it must not panic: a fold body runs inside the generated parser and, under
/// `codegen-backend = "cranelift"`, a panic ABORTS the process rather than failing the fold.
#[test]
fn a_byte_method_at_the_wrong_carrier_is_the_error_term() {
    for source in [
        r#"b"dead".hexToBytes()"#,   // hexToBytes wants a String
        r#""dead".bytesToHex()"#,    // bytesToHex wants a ByteArray
        r#"b"dead".toUtf8Bytes()"#,  // toUtf8Bytes wants a String
        r#"7.bytesToHex()"#,
        r#"7.hexToBytes()"#,
        r#"7.toUtf8Bytes()"#,
    ] {
        assert!(
            matches!(fold(source), Proc::Err),
            "`{source}` is out of domain and must fold to the `error` term; got {:?}",
            fold(source),
        );
    }
}
