//! NUMERIC-LITERAL CARRIER INVARIANT — a numeral's carrier is a function of the numeral
//! TEXT, and no reading of a canonical surface re-spells a token.
//!
//! # The defect this file pins (2026-07-27)
//!
//! `languages::gen_calculator_prop::bigrat_display_parse_roundtrip` failed on
//!
//! ```text
//!     MulBigRat(MulBigRat(AddBigRat(RatLit 1501459918, RatLit 1779999505),
//!                         RatLit 280584074),
//!               BitAndBigRat(FixedToBigRat(FixedLit 1388007349p0),
//!                            FixedToBigRat(FixedLit -260592200p0)))
//! ```
//!
//! with a **cross-factor coupling**: appending a third factor to a product flipped the
//! carrier the FIRST factor elected, and with it the surface.
//!
//! ```text
//!     "(0 + 0) * 0u32"                     ⇒ IntToBigRat(AddInt 0 0)      ⇒ "(0 + 0) * 0u32"
//!     "(0 + 0) * 0u32 * (0p0 bitand 0p0)"  ⇒ UInt32ToBigRat(AddUInt32 0 0)
//!                                          ⇒ "(0u32 + 0u32) * 0u32 * (0p0 bitand 0p0)"
//! ```
//!
//! Two structurally identical operands, two different carriers, chosen by what stood to
//! their right — so `Display ∘ Parse` had no fixpoint at depth 1 and the property's
//! `display(parse(display(parse(display(t))))) == display(parse(display(t)))` failed.
//!
//! ## The mechanism, named
//!
//! | layer | file:line | what it did |
//! |---|---|---|
//! | ROOT | `languages/src/calculator.rs` — `literals { UInt32 { … } }` | `pattern` declares a MANDATORY `u32` tail; `eval` was `parse_int_lit(text, None)`, a **universal acceptor of every integer spelling** |
//! | consequence | generated `display.rs` — `UInt32::NumLit(v)` | writes `format!("{}u32", v)` — always the tail, because the pattern says so |
//! | amplifier | generated `wpda.rs` — `__mettail_wpda_select_min_weight_realizing` | elects ONE derivation by **global argmin over whole-derivation `LexicographicWeight`** |
//!
//! A category's literal domain is decided by its own `eval` and by nothing else
//! (`macros/src/gen/runtime/wpda_codegen/prefix.rs:386`). So the acceptor admitted a bare
//! numeral as a `UInt32::NumLit` while `Display` wrote it back **with** the tail:
//!
//! ```text
//!     UInt32::parse("7")                ⇒ Ok(NumLit(7))     ← accepted WITHOUT the tail
//!     format!("{}", UInt32::NumLit(7))  ⇒ "7u32"            ← written back WITH it
//! ```
//!
//! That put a term in the SPPF **whose display is not the surface it was parsed from**.
//! `"0 + 0"` in a `BigRat` position then carried four readings —
//!
//! ```text
//!     AddBigRat(IntToBigRat 0, IntToBigRat 0)                    display "0 + 0"
//!     IntToBigRat(AddInt 0 0)                                    display "0 + 0"
//!     BigIntToBigRat(AddBigInt(IntToBigInt 0, IntToBigInt 0))     display "0 + 0"
//!     UInt32ToBigRat(AddUInt32 0 0)                              display "0u32 + 0u32"   ← the intruder
//! ```
//!
//! — and because the election minimises a weight of the WHOLE derivation, which of the
//! four won was a function of the whole expression. The election is global **by design**;
//! it only becomes visible as a surface change when the alternative set contains a
//! reading that is not surface-faithful.
//!
//! ## The direction ruling
//!
//! Neither of the two obvious directions is the root.
//!
//! * **`Display` is NOT lossy here.** `UInt32::NumLit(7) ⇄ "7u32"` is exact in both
//!   directions, and the intruding reading `UInt32ToBigRat(AddUInt32 0 0)` re-parses from
//!   its own display `"0u32 + 0u32"` on the nose. This is *not* an extension of the
//!   auto-injection non-injectivity documented in
//!   `languages/tests/display_parse_term_preservation.rs`: that region is where several
//!   terms share ONE surface, which is harmless for a fixpoint. Here ONE term had a
//!   surface **other than the one it was parsed from** — the opposite failure.
//! * **The ELECTION is not the wrong answer, it is the wrong layer.** Teaching the
//!   elector to prefer a reading whose display equals the input would be a post-hoc
//!   surface filter over readings the grammar should never have admitted — the mistake
//!   `languages/src/rhocalc.rs:129` already names, in the identical defect for `BigInt`.
//! * **The LITERAL ACCEPTOR is the root**: an `eval` strictly wider than its own declared
//!   `pattern`. `BigInt`'s copy of this defect was fixed in the same file on 2026-07-25
//!   (divergence I, Stage A); `UInt32` was the one integer category left with it.
//!
//! # The invariants pinned here
//!
//! | # | invariant | why it is the right one |
//! |---|---|---|
//! | I1 | every numeral text has at most ONE literal carrier, and it is a function of the text | no election over carriers can exist to be context-sensitive |
//! | I2 | `UInt32` accepts EXACTLY its declared `…u32` domain | the root, stated directly |
//! | I3 | no reading of a surface RE-SPELLS a token (grouping may differ, tokens may not) | the election stays global and free to move; the PROGRAM cannot move with it |
//! | I4 | `Display ∘ Parse` is a fixpoint from layer 1 for the seed and its family | the failing property, pinned by construction rather than by a random draw |
//! | I5 | a factor's carrier does not depend on what stands to its right | the coupling, stated directly |
//!
//! I3 is deliberately **narrower** than "all readings of a surface display the same",
//! which was the first formulation tried here and is measurably FALSE: readings legally
//! differ in inert `(` … `)` grouping, because a cross-category projection operand is
//! bracketed by its source category's precedence logic. It is also narrower than "the
//! election is context-free" — the election is still global, and that is correct. What
//! the fix restores is that its freedom is *unobservable in the token stream*.
//!
//! A SECOND, distinct literal asymmetry — calculator's `BigRat` literal `Display` DROPPED
//! the `r` its pattern makes mandatory — is the MIRROR of the one fixed here: a `Display`
//! narrower than its acceptor, rather than an acceptor wider than its `Display`. It was
//! closed on the same day and is pinned by
//! [`bigrat_literal_display_writes_its_declared_r_tail`], which also records that its
//! consequence was a wrong NUMBER, not a wrong spelling: `RatLit 3/4` displayed `3/4`,
//! which `Int` reads as integer division, value 0.
//!
//! The sweep that proves there is no THIRD instance — in either direction, in any
//! language — is `languages/tests/literal_domain_agreement.rs`.
//!
//! # Non-vacuity
//!
//! `negative_control_*` proves the corpus really is ambiguous (I3 would otherwise hold
//! vacuously, and "collapse the ambiguity" is the wrong fix this file rules out), that
//! `UInt32` still accepts something (I2 is not satisfied by a category that rejects
//! everything), that the trajectory harness can see a surface move (I4 is not satisfied by
//! a constant), and that the historical wrong answer is named on its own.

#![cfg(feature = "calculator")]

use mettail_languages::calculator::{BigInt, BigRat, Fixed, Float, Int, UInt32};
use std::sync::Arc;

// ═══════════════════════════════════════════════════════════════════════════
// Harness
// ═══════════════════════════════════════════════════════════════════════════

/// The literal carriers of one numeral text: the categories whose parse of `text` yields
/// **that category's own literal constructor**, not a cross-category cast of someone
/// else's literal. `BigRat::parse("7")` succeeds via `IntToBigRat(NumLit 7)` — that is a
/// cast, and counting it would measure category REACHABILITY instead of the literal
/// domain the invariant is about.
fn literal_carriers(text: &str) -> Vec<&'static str> {
    // Six numeric categories; a well-formed numeral lands in exactly one.
    let mut out = Vec::with_capacity(6);
    if matches!(Int::parse(text), Ok(Int::NumLit(_))) {
        out.push("Int");
    }
    if matches!(UInt32::parse(text), Ok(UInt32::NumLit(_))) {
        out.push("UInt32");
    }
    if matches!(BigInt::parse(text), Ok(BigInt::NumLit(_))) {
        out.push("BigInt");
    }
    if matches!(BigRat::parse(text), Ok(BigRat::RatLit(_))) {
        out.push("BigRat");
    }
    if matches!(Fixed::parse(text), Ok(Fixed::FixedLit(_))) {
        out.push("Fixed");
    }
    if matches!(Float::parse(text), Ok(Float::FloatLit(_))) {
        out.push("Float");
    }
    out
}

/// How many `display ∘ parse` steps every trajectory below is walked for. Three is one
/// more than the property needs (`s1 == s2`), so a surface that oscillates with period 2
/// instead of settling is caught rather than mistaken for a fixpoint.
const TRAJECTORY_STEPS: usize = 3;

/// Walk `display ∘ parse` from `start` for exactly [`TRAJECTORY_STEPS`] steps and report
/// every surface it passes through, `s0 … s3`.
///
/// It deliberately does NOT stop early at a repeat: a short vector would make the
/// comparison below index out of bounds precisely on the surfaces that are already
/// well-behaved, which is the wrong way round for a regression guard.
fn display_parse_trajectory(start: &str) -> Vec<String> {
    let mut seen = Vec::with_capacity(TRAJECTORY_STEPS + 1);
    seen.push(start.to_string());
    for _ in 0..TRAJECTORY_STEPS {
        let surface = seen.last().expect("seeded with s0").clone();
        let term = BigRat::parse(&surface)
            .unwrap_or_else(|e| panic!("surface {surface:?} must keep parsing: {e}"));
        seen.push(format!("{term}"));
    }
    seen
}

/// Render a trajectory for a failure message.
fn show(trajectory: &[String]) -> String {
    trajectory
        .iter()
        .enumerate()
        .map(|(i, s)| format!("      s{i} = {s:?}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A surface stripped of everything that is INERT — whitespace and the language's pure
/// `(` … `)` grouping, which denotes nothing
/// (`languages/tests/calculator_grouping_is_inert.rs`).
///
/// Two readings of one surface are allowed to disagree about grouping: a cross-category
/// projection operand is bracketed by the SOURCE category's own precedence logic, so
/// `AddBigRat(IntToBigRat(AddInt 1 2), IntToBigRat 3)` writes `"(1 + 2) + 3"` where
/// `IntToBigRat(AddInt(AddInt 1 2, 3))` writes `"1 + 2 + 3"`. Both denote the same sum and
/// both re-parse. What they may NOT disagree about is the spelling of a TOKEN — and a
/// numeral acquiring a `u32` tail is exactly such a disagreement.
fn modulo_inert_grouping(surface: &str) -> String {
    surface.chars().filter(|c| !c.is_whitespace() && *c != '(' && *c != ')').collect()
}

/// The exact shrunken proptest seed, rebuilt from its `Debug`.
fn seed_term() -> BigRat {
    fn rat(n: i64) -> Arc<BigRat> {
        Arc::new(BigRat::RatLit(
            mettail_runtime::CanonicalBigRat::try_from_nd(n.into(), 1.into())
                .expect("whole rational"),
        ))
    }
    fn fixed(text: &str) -> Arc<BigRat> {
        Arc::new(BigRat::FixedToBigRat(Arc::new(Fixed::FixedLit(
            mettail_runtime::parse_fixed_lit(text).expect("fixed-point literal"),
        ))))
    }
    BigRat::MulBigRat(
        Arc::new(BigRat::MulBigRat(
            Arc::new(BigRat::AddBigRat(rat(1_501_459_918), rat(1_779_999_505))),
            rat(280_584_074),
        )),
        Arc::new(BigRat::BitAndBigRat(fixed("1388007349p0"), fixed("-260592200p0"))),
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// I2 — the ROOT, stated directly
// ═══════════════════════════════════════════════════════════════════════════

/// `UInt32`'s `eval` accepts EXACTLY the spellings its `pattern` declares.
///
/// The declared pattern is `(<radix-or-decimal digits>)u32` — the `u32` tail is
/// MANDATORY and there is no sign. Every row below is decided by the token TEXT alone.
#[test]
fn uint32_literal_accepts_exactly_its_declared_u32_domain() {
    // ACCEPTED — carries the declared tail and fits `u32`.
    for (text, value) in
        [("0u32", 0u32), ("7u32", 7), ("0x1Fu32", 31), ("0b101u32", 5), ("0o17u32", 15),
         ("4294967295u32", u32::MAX), ("1_0u32", 10)]
    {
        assert_eq!(
            UInt32::parse(text).map(|t| format!("{t:?}")).as_deref(),
            Ok(format!("NumLit({value})").as_str()),
            "`{text}` carries the declared `u32` tail and fits u32; it must be a UInt32 literal"
        );
    }

    // REJECTED — no declared tail. Each of these HAS a carrier; it is simply not this one.
    for text in ["0", "7", "7i32", "7n", "7r", "7p0", "7.5", "3000000000", "0x1F"] {
        assert!(
            !matches!(UInt32::parse(text), Ok(UInt32::NumLit(_))),
            "`{text}` does not carry the declared `u32` tail and must NOT be a UInt32 literal, \
             got {:?}",
            UInt32::parse(text).map(|t| format!("{t:?}"))
        );
    }

    // REJECTED — declared tail, but the value overflows the declared width. Fail-closed
    // and text-determined, exactly as Rust rejects `5000000000u32`.
    for text in ["4294967296u32", "5000000000u32"] {
        assert!(
            UInt32::parse(text).is_err(),
            "`{text}` overflows u32 and must be rejected outright, got {:?}",
            UInt32::parse(text).map(|t| format!("{t:?}"))
        );
    }

    // …and the tail Display writes is the tail the acceptor demands, so the literal
    // round-trips through its own surface.
    for value in [0u32, 7, 4_294_967_295] {
        let lit = UInt32::NumLit(value);
        let surface = format!("{lit}");
        assert_eq!(surface, format!("{value}u32"), "Display must write the declared tail");
        assert_eq!(
            format!("{:?}", UInt32::parse(&surface).expect("its own surface must parse")),
            format!("{lit:?}"),
            "the literal must be recovered from its own display"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// I1 — one numeral, one carrier, chosen by the TEXT
// ═══════════════════════════════════════════════════════════════════════════

/// The carrier table. Every spelling maps to at most one literal category, and which one
/// depends on the text and on nothing else — no context, no parentheses, no election.
///
/// `None` means "no literal carrier": either the spelling is a compound (`-7` is
/// `Neg` applied to `7`, because calculator's `Int` pattern carries no sign) or it is
/// fail-closed (`5000000000u32` overflows its declared width).
#[test]
fn numeral_carrier_is_a_function_of_the_text() {
    let table: &[(&str, Option<&str>)] = &[
        // unsuffixed / `i32` — Int, while it fits i32
        ("0", Some("Int")),
        ("7", Some("Int")),
        ("7i32", Some("Int")),
        ("0x1F", Some("Int")),
        ("2147483647", Some("Int")),
        // unsuffixed overflow — BigInt's declared superset
        ("3000000000", Some("BigInt")),
        ("4294967296", Some("BigInt")),
        // `u32` — UInt32 (the row the fix restored)
        ("0u32", Some("UInt32")),
        ("7u32", Some("UInt32")),
        ("0x1Fu32", Some("UInt32")),
        ("4294967295u32", Some("UInt32")),
        // `n` — BigInt
        ("7n", Some("BigInt")),
        ("-7n", Some("BigInt")),
        // `r` — BigRat
        ("7r", Some("BigRat")),
        ("3r/4r", Some("BigRat")),
        // `p<scale>` — Fixed
        ("7p0", Some("Fixed")),
        ("-260592200p0", Some("Fixed")),
        // decimal / exponent — Float
        ("7.5", Some("Float")),
        ("1e3", Some("Float")),
        // no literal carrier
        ("-7", None),
        ("5000000000u32", None),
    ];

    let mut wrong = Vec::with_capacity(table.len());
    for (text, expected) in table {
        let got = literal_carriers(text);
        let ok = match expected {
            Some(cat) => got.as_slice() == [*cat],
            None => got.is_empty(),
        };
        if !ok {
            wrong.push(format!(
                "  {text:>16} — expected {}, got {got:?}",
                expected.map(|c| format!("[{c:?}]")).unwrap_or_else(|| "no carrier".to_string()),
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "the carrier of a numeral must be a function of its TEXT; {} row(s) disagree:\n{}",
        wrong.len(),
        wrong.join("\n"),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// I3 — no reading of a surface RE-SPELLS a numeral
// ═══════════════════════════════════════════════════════════════════════════

/// **The reading-level guard, stated at exactly the strength that holds.**
///
/// The first formulation attempted here — "every reading of one surface has the same
/// display" — is FALSE, and measurably so: `"1 + 2 + 3"` has six readings, three writing
/// `"1 + 2 + 3"` and three writing `"(1 + 2) + 3"`. That difference is legitimate and is
/// a *fix*, not a defect: a cross-category projection operand is bracketed by the SOURCE
/// category's own precedence logic
/// (`languages/tests/display_parse_term_preservation.rs`, defect 1), so the reading
/// `AddBigRat(IntToBigRat(AddInt 1 2), …)` must show where its `Int`-level sum ends.
/// Parentheses are the language's pure grouping and denote nothing
/// (`languages/tests/calculator_grouping_is_inert.rs`), so a reading is free to add them.
///
/// What no reading may do is change a TOKEN. The defect was a bare numeral coming back
/// spelled `0u32` — a different token, from an acceptor that took a spelling its own
/// `Display` never writes. So the invariant is stated **modulo inert grouping**:
///
/// ```text
///     ∀ surface s. let c = display(parse(s)).            ← the CANONICAL spelling
///         ∀ reading r ∈ readings(c).
///             modulo_inert_grouping(display(r)) == modulo_inert_grouping(c)
/// ```
///
/// This is strictly weaker than display equality (it permits the bracketing fix) and
/// strictly stronger than "some reading round-trips" (it admits no intruder at all). It
/// is what makes a GLOBAL elector safe: the election may move freely inside the class of
/// readings, and no motion of it can re-spell the program.
///
/// ## Why the surface is CANONICALISED first
///
/// The invariant is asserted of `canonical = display(parse(s))`, not of `s`. A numeral may
/// legitimately be written in a spelling `Display` does not choose, and re-writing it is a
/// deliberate NORMALISATION inside one carrier, not a change of carrier:
///
/// ```text
///     "0x1F + 1"        ⇒ "31 + 1"           radix normalised to decimal (still Int)
///     "3000000000 + 1"  ⇒ "3000000000n + 1"  BigInt's declared unsuffixed-overflow
///                                            superset written back with its `n` tail
/// ```
///
/// (Before 2026-07-27 `"3r/4r + 1"` normalised to `"3/4 + 1"` and belonged in that table
/// too. It no longer moves at all: the rational keeps its declared spelling —
/// [`bigrat_literal_display_writes_its_declared_r_tail`].)
///
/// Canonicalising first is also the exact domain the round-trip property lives on: it
/// never hands `parse` anything other than a string `display` produced. Asserting over raw
/// user spellings would be asserting that `Display` has no canonical form, which is not
/// the claim — and would have hidden the real one behind three false alarms.
#[test]
fn no_reading_of_a_canonical_numeric_surface_respells_a_numeral() {
    let surfaces = [
        "0 + 0",
        "1 + 2",
        "1 + 2 + 3",
        "(0 + 0) * 0u32",
        "(0 + 0) * 0u32 * (0p0 bitand 0p0)",
        "(1501459918 + 1779999505) * 280584074u32 * (1388007349p0 bitand -260592200p0)",
        "1 * 2 bitand 3",
        "1 + 2u32",
        // The four spellings Display normalises — included precisely BECAUSE they move,
        // so the canonicalisation step is exercised rather than assumed away.
        "0x1F + 1",
        "3000000000 + 1",
        "7r + 1",
        "3r/4r + 1",
    ];

    let mut failures = Vec::with_capacity(surfaces.len());
    for surface in surfaces {
        let canonical = format!(
            "{}",
            BigRat::parse(surface).unwrap_or_else(|e| panic!("{surface:?} must parse: {e}"))
        );
        let alts = BigRat::parse_via_wpda_all(&canonical)
            .unwrap_or_else(|e| panic!("{canonical:?} must parse: {e:?}"));
        assert!(!alts.is_empty(), "{canonical:?} produced no readings at all");
        let want = modulo_inert_grouping(&canonical);
        let mut rows: Vec<String> = alts
            .iter()
            .filter(|a| modulo_inert_grouping(&format!("{a}")) != want)
            .map(|a| format!("      {:?}   ⇐ {a:?}", format!("{a}")))
            .collect();
        if !rows.is_empty() {
            rows.sort();
            rows.dedup();
            failures.push(format!(
                "  {surface:?} ⇒ canonical {canonical:?} — {} of {} readings re-spell a token:\n{}",
                rows.len(),
                alts.len(),
                rows.join("\n")
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "no reading of a CANONICAL numeric surface may re-spell a token (grouping may differ, \
         tokens may not); {} surface(s) carry an intruder:\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// I5 — the cross-factor coupling, stated directly
// ═══════════════════════════════════════════════════════════════════════════

/// A factor's carrier does not depend on what stands to its right.
///
/// The rows share the prefix `(A + B) * Cu32` and differ only in what is appended. Before
/// the fix the two-factor row elected `IntToBigRat(AddInt …)` and the three-factor row
/// elected `UInt32ToBigRat(AddUInt32 …)` — from the SAME prefix bytes.
#[test]
fn a_factors_carrier_does_not_depend_on_a_later_factor() {
    // Both the minimal `0`-form and the shrunken seed's numerals, so a fix that only
    // happened to work at zero is caught.
    for (prefix, suffixes) in [
        ("(0 + 0) * 0u32", ["", " * (0p0 bitand 0p0)", " * 1r", " + 0p0"]),
        (
            "(1501459918 + 1779999505) * 280584074u32",
            ["", " * (1388007349p0 bitand -260592200p0)", " * 1r", " + 0p0"],
        ),
    ] {
        // The carrier the prefix elects when it stands alone is the reference.
        let alone = BigRat::parse(prefix).unwrap_or_else(|e| panic!("{prefix:?}: {e}"));
        let reference = first_factor_debug(&alone);

        for suffix in suffixes {
            let whole = format!("{prefix}{suffix}");
            let parsed = BigRat::parse(&whole).unwrap_or_else(|e| panic!("{whole:?}: {e}"));
            assert_eq!(
                first_factor_debug(&parsed),
                reference,
                "appending {suffix:?} changed the carrier the prefix {prefix:?} elects — \
                 a later factor must not reach back into an earlier one\n  whole: {whole:?}\n  \
                 term : {parsed:?}"
            );
        }
    }
}

/// The leftmost leaf of a left-nested `MulBigRat` spine — the "first factor" the coupling
/// moved. Returns its `Debug`, which names the carrier (`IntToBigRat(AddInt …)` vs
/// `UInt32ToBigRat(AddUInt32 …)`) without this test having to enumerate the tower.
fn first_factor_debug(term: &BigRat) -> String {
    let mut cursor = term;
    loop {
        match cursor {
            BigRat::MulBigRat(left, _) | BigRat::AddBigRat(left, _) => cursor = left,
            other => return format!("{other:?}"),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// I4 — the failing property, pinned by construction
// ═══════════════════════════════════════════════════════════════════════════

/// The exact seed `gen_calculator_prop::bigrat_display_parse_roundtrip` shrank to.
///
/// `Display` is not injective on this term — `RatLit 7` and `IntToBigRat(NumLit 7)` share
/// the surface `7`, which the auto-injection lattice declares
/// (`languages/tests/display_parse_term_preservation.rs`). So the term is NOT asserted to
/// come back. What IS asserted is the property that failed: after ONE parse the surface
/// stops moving.
#[test]
fn the_seed_terms_surface_stops_moving_after_one_parse() {
    mettail_runtime::clear_var_cache();
    let term = seed_term();
    let s0 = format!("{term}");
    // ★ GOLDEN RE-DERIVED 2026-07-27. Was
    //   "(1501459918 + 1779999505) * 280584074 * 1388007349p0 bitand -260592200p0"
    // — the three `RatLit`s wrote NO `r`, because calculator's `BigRat` Display omitted
    // the tail its own pattern makes mandatory (the residual this file used to pin as a
    // measured fact). With that closed, each rational carries its declared `r`. Only the
    // three rational spellings moved; the two `p0` fixed-point literals and the whole
    // operator/grouping structure are unchanged.
    assert_eq!(
        s0, "(1501459918r + 1779999505r) * 280584074r * 1388007349p0 bitand -260592200p0",
        "the seed's own surface moved; the rest of this test would be measuring something else"
    );

    // s0 = display(t); s1 = display(parse(s0)); s2 = display(parse(s1)); …
    // The failing property is exactly `s1 == s2`; `s2 == s3` additionally rules out a
    // period-2 oscillation being mistaken for convergence.
    let trajectory = display_parse_trajectory(&s0);
    assert_eq!(
        trajectory[1],
        trajectory[2],
        "Display/Parse must be a fixpoint from the FIRST parse onward. Trajectory:\n{}",
        show(&trajectory),
    );
    assert_eq!(
        trajectory[2],
        trajectory[3],
        "…and it must STAY there, rather than oscillate. Trajectory:\n{}",
        show(&trajectory),
    );
    // …and the historical wrong answer must not be reachable at any layer.
    for (i, s) in trajectory.iter().enumerate() {
        assert!(
            !s.contains("1501459918u32"),
            "layer s{i} re-spelled the first factor as a UInt32 literal: {s:?}\n{}",
            show(&trajectory),
        );
    }
}

/// The same property over a family the seed is one member of, so the pin is not a single
/// string. Each row is a `BigRat` surface whose numerals sit in operand positions the
/// tower can re-carry.
#[test]
fn the_numeric_towers_surface_stops_moving_after_one_parse() {
    let surfaces = [
        "0 + 0",
        "(0 + 0) * 0u32",
        "(0 + 0) * 0u32 * (0p0 bitand 0p0)",
        "(0 + 0) * (0 + 0) * (0 + 0)",
        "(1 + 2) * 3 * (4p0 bitand 5p0)",
        "(1 + 2) * 3u32 * 4r",
        "1 + 2 * 3 bitand 4",
        "(3000000000 + 1) * 2",
        "-(1 + 2) * 3",
    ];
    let mut failures = Vec::with_capacity(surfaces.len());
    for surface in surfaces {
        mettail_runtime::clear_var_cache();
        let trajectory = display_parse_trajectory(surface);
        if trajectory[1] != trajectory[2] || trajectory[2] != trajectory[3] {
            failures.push(format!("  {surface:?}\n{}", show(&trajectory)));
        }
    }
    assert!(
        failures.is_empty(),
        "Display/Parse must be a fixpoint from the first parse onward; {} surface(s) keep \
         moving:\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// THE MIRROR DEFECT — closed 2026-07-27
// ═══════════════════════════════════════════════════════════════════════════

/// ★ **The MIRROR of the defect this file guards, and it is now CLOSED.**
///
/// | | acceptor | `Display` | symptom |
/// |---|---|---|---|
/// | `UInt32` | was WIDER — took a bare numeral | writes the declared `u32` tail | a bare numeral came back re-spelled ⇒ **no fixpoint** |
/// | `BigRat` | exactly the declared `…r(/…r)?` domain | was NARROWER — dropped the `r` | `RatLit 3/4` displayed `3/4`, which `Int` reads as **integer division ⇒ the VALUE 0** |
///
/// Both are one invariant — a category's `eval`, its `pattern` and its `Display` must
/// describe ONE language — violated in opposite directions.
///
/// ## What was wrong, and why it was worse than a spelling
///
/// `Display` wrote `format!("{}", v)`: no tail at all. Two independent reasons, both in
/// `macros/src/gen/syntax/display.rs`, and BOTH had to be fixed:
///
/// 1. `mandatory_literal_tail_of_pattern`'s backward literal scan saw the trailing `?` of
///    the optional composite group `(/(…)r)?` and refused. Now
///    `composite_repeat_of_optional_group` strips a `?`-quantified balanced group and
///    proves the tail is still mandatory by requiring the group's body to end with it.
/// 2. the sign side condition refused any tail for a signed payload whose pattern has no
///    `-?`, on the stated grounds that the grammar had "no unary-minus rule to read at
///    the category" — which it never checked. Calculator HAS
///    `NegBigRat . a:BigRat |- "-" a : BigRat`, so `category_has_unary_minus_rule` now
///    tests the grammar instead of assuming.
///
/// And the tail could not simply be appended: `CanonicalBigRat` renders `3/4`, so
/// `format!("{}r", v)` would give `3/4r`, which is not a word of the pattern either. The
/// tail belongs to each COMPONENT of the composite — `3r/4r` — with the separator taken
/// from the pattern's own optional group.
///
/// The consequence of the old behaviour was not cosmetic. `3/4` is not a rational at
/// `Int`; it is integer division:
///
/// ```text
///     RatLit 3/4  ─display→  "3/4"  ─parse→  IntToBigRat(DivInt 3 4)  ─eval→  0
/// ```
///
/// so a displayed rational, read back, was a DIFFERENT NUMBER.
#[test]
fn bigrat_literal_display_writes_its_declared_r_tail() {
    fn rat_lit(numer: i64, denom: i64) -> BigRat {
        BigRat::RatLit(
            mettail_runtime::CanonicalBigRat::try_from_nd(numer.into(), denom.into())
                .expect("well-formed rational"),
        )
    }

    // The whole and composite spellings the pattern `(…)r(/(…)r)?` declares.
    assert_eq!(format!("{}", rat_lit(0, 1)), "0r");
    assert_eq!(format!("{}", rat_lit(7, 1)), "7r");
    assert_eq!(
        format!("{}", rat_lit(3, 4)),
        "3r/4r",
        "the tail belongs to each COMPONENT of the composite, not to the rendering"
    );
    // The sign is detached — the pattern has no `-?` — and `NegBigRat` reads it.
    assert_eq!(format!("{}", rat_lit(-7, 1)), "-7r");
    assert_eq!(format!("{}", rat_lit(-1, 2)), "-1r/2r");

    // Acceptor and Display now describe the same language, in both directions.
    for (numer, denom) in [(0i64, 1i64), (7, 1), (3, 4), (22, 7)] {
        mettail_runtime::clear_var_cache();
        let lit = rat_lit(numer, denom);
        let surface = format!("{lit}");
        assert_eq!(
            format!("{:?}", BigRat::parse(&surface).expect("its own surface must parse")),
            format!("{lit:?}"),
            "the rational must be recovered from its own display ({surface:?})"
        );
    }
    assert!(
        !matches!(BigRat::parse("7"), Ok(BigRat::RatLit(_))),
        "a bare numeral must still NOT be a BigRat literal; it reaches BigRat by injection"
    );

    // ★ THE VALUE, not the spelling. Before the fix this round-tripped to zero.
    let three_quarters = rat_lit(3, 4);
    let recovered = BigRat::parse(&format!("{three_quarters}")).expect("must parse");
    assert_eq!(
        format!("{recovered:?}"),
        "RatLit(Ratio { numer: 3, denom: 4 })",
        "a displayed rational must read back as the SAME NUMBER, not as integer division"
    );
    assert!(
        !format!("{recovered:?}").contains("DivInt"),
        "the composite must not be read as Int division: {recovered:?}"
    );

    // Negatives round-trip through the declared unary-minus rule: a different term, the
    // same denotation, and a surface that is a fixpoint from the first parse.
    for term in [rat_lit(-7, 1), rat_lit(-1, 2)] {
        mettail_runtime::clear_var_cache();
        let surface = format!("{term}");
        let back = BigRat::parse(&surface).expect("the negative rational must parse");
        assert!(
            format!("{back:?}").starts_with("NegBigRat(RatLit("),
            "the detached sign must be read by `NegBigRat`, keeping the BigRat carrier: {back:?}"
        );
        assert_eq!(format!("{back}"), surface, "…and re-display to the same surface");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// NEGATIVE CONTROLS — the assertions above must be able to FAIL
// ═══════════════════════════════════════════════════════════════════════════

/// NC1 — the corpus of [`no_reading_of_a_canonical_numeric_surface_respells_a_numeral`] is really
/// AMBIGUOUS. If the tower had collapsed to one reading per surface that test would hold
/// vacuously and would stop guarding anything — and "collapse the ambiguity" is precisely
/// the wrong fix this file exists to rule out.
#[test]
fn negative_control_the_numeric_tower_is_still_ambiguous() {
    let multi: Vec<(&str, usize)> = ["0 + 0", "1 + 2", "(0 + 0) * 0u32"]
        .into_iter()
        .map(|s| {
            (s, BigRat::parse_via_wpda_all(s).map(|a| a.len()).unwrap_or(0))
        })
        .collect();
    assert!(
        multi.iter().all(|(_, n)| *n >= 2),
        "the tower must still offer several readings per surface, else the token-preservation \
         invariant is vacuous: {multi:?}"
    );
    // …and at least one surface must offer readings with genuinely different SHAPES,
    // not N copies of one term.
    let alts = BigRat::parse_via_wpda_all("0 + 0").expect("`0 + 0` must parse");
    let shapes: std::collections::BTreeSet<String> =
        alts.iter().map(|a| format!("{a:?}")).collect();
    assert!(
        shapes.len() >= 2,
        "the readings of `0 + 0` must be structurally distinct, got {shapes:?}"
    );
}

/// NC2 — `UInt32` still accepts something. A category whose `eval` rejected EVERYTHING
/// would satisfy the rejection half of I2 and the whole carrier table, while making the
/// `u32` surface unparseable.
#[test]
fn negative_control_uint32_still_has_a_literal_surface() {
    assert!(
        matches!(UInt32::parse("7u32"), Ok(UInt32::NumLit(7))),
        "the declared `…u32` domain must still be ACCEPTED, got {:?}",
        UInt32::parse("7u32").map(|t| format!("{t:?}"))
    );
    // …and it is reachable from inside an expression, not only at top level.
    let inside = BigRat::parse("1r + 7u32").expect("`1r + 7u32` must parse");
    assert!(
        format!("{inside:?}").contains("UInt32ToBigRat(NumLit(7))"),
        "a `u32` literal must still be readable as a BigRat operand: {inside:?}"
    );
}

/// NC3 — the trajectory harness can SEE a surface move.
///
/// Every trajectory above asserts `s1 == s2`, which a harness that returned a constant
/// vector would satisfy. This control feeds it a surface that genuinely moves at the
/// FIRST step and asserts the harness reports `s0 != s1`. Motion at s0→s1 is legal; it is
/// motion at s1→s2 that the property forbids.
///
/// ★ MOVER RE-DERIVED 2026-07-27. This used to be `"7r + 1"`, which moved because
/// calculator's `BigRat` Display dropped the `r` its pattern declares. That defect is
/// closed ([`bigrat_literal_display_writes_its_declared_r_tail`]) and `"7r + 1"` is now a
/// fixpoint at s0, which would make this control prove nothing. The replacement is a
/// RADIX spelling: `0x1F` is a legal `Int` word that `Display` does not choose, so it
/// normalises to decimal on the first parse — a canonicalisation, which is the same class
/// of legal first-step motion and one that no bug fix will remove.
#[test]
fn negative_control_trajectory_detects_a_moving_surface() {
    let trajectory = display_parse_trajectory("0x1F + 1");
    assert_eq!(trajectory.len(), TRAJECTORY_STEPS + 1, "the harness must walk every step");
    assert_ne!(
        trajectory[0],
        trajectory[1],
        "this control needs a surface that MOVES at the first parse, else it proves the \
         harness nothing:\n{}",
        show(&trajectory),
    );
    assert_eq!(
        trajectory[1],
        trajectory[2],
        "…and having moved once it must then stop:\n{}",
        show(&trajectory),
    );
}

/// NC4 — the historical wrong answer is stated on its own, so a regression names the
/// defect instead of diffing two long strings. A bare numeral must never be re-spelled
/// with a `u32` tail by a round-trip.
#[test]
fn negative_control_a_bare_numeral_never_acquires_a_u32_tail() {
    for surface in ["0 + 0", "(0 + 0) * 0u32 * (0p0 bitand 0p0)", "1 + 2 + 3"] {
        let once = format!("{}", BigRat::parse(surface).expect("must parse"));
        let twice = format!("{}", BigRat::parse(&once).expect("must re-parse"));
        for (label, s) in [("first", &once), ("second", &twice)] {
            assert!(
                !s.contains("0u32 + ") && !s.contains("1u32") && !s.contains("2u32"),
                "the {label} display of {surface:?} grew a `u32` tail on a bare numeral: {s:?}"
            );
        }
    }
}
