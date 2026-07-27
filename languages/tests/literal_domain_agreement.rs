//! LITERAL-DOMAIN AGREEMENT — a category's `eval`, its declared `pattern` and its
//! `Display` must describe ONE language, and every language's literal categories are
//! swept for both directions of disagreement.
//!
//! # Why a sweep rather than a third individual discovery
//!
//! The same invariant was violated twice in `languages/src/calculator.rs`, in opposite
//! directions, and each was found only when a proptest happened to draw the right term:
//!
//! | | acceptor vs. `Display` | symptom |
//! |---|---|---|
//! | `UInt32` (fixed 2026-07-27) | acceptor WIDER — took a bare numeral its `Display` never writes | a bare numeral came back spelled `0u32`; the global election made an earlier factor's carrier depend on a later one |
//! | `BigRat` (fixed 2026-07-27) | `Display` WIDER — wrote `3/4`, outside its own `(…)r(/(…)r)?` | `3/4` is `Int` division: `RatLit 3/4` round-tripped to the VALUE 0 |
//!
//! A third would have cost another proptest draw. This file is the instrument instead:
//! it enumerates every literal category of every language and asserts both directions,
//! so a new violation fails HERE, by name, on the first run.
//!
//! # The two directions, as assertions
//!
//! ```text
//!   A1  Display ⊆ acceptor      ∀ v.  parse(display(Lit v)) = Lit v
//!   A2  carriers are disjoint   ∀ text.  |{ Cat : parse_Cat(text) = Cat::Lit _ }| ≤ 1
//! ```
//!
//! A1 says every word `Display` writes is one the category itself reads back. A2 says a
//! numeral's carrier is a function of its TEXT — the property that makes a global
//! disambiguating election unobservable in the surface
//! (`languages/tests/numeric_literal_carrier_is_text_determined.rs` pins the
//! consequences for calculator; this file pins the premise for every language).
//!
//! # Declared exceptions
//!
//! Both assertions carry an explicit exception table. Every row is TYPED, so no row can
//! be a shrug:
//!
//! * [`Exception::SignIsAnOperator`] — the pattern deliberately excludes a leading `-`
//!   (calculator's `Int`: "unary minus is an operator, not a signed literal"), so
//!   `Display` writes a detached sign that the category's own unary-minus rule reads.
//!   This is NOT waved through: the row asserts the recovered term has the SAME
//!   DENOTATION and that the surface is a fixpoint from the first parse.
//! * [`Exception::NoSurface`] — the declared pattern cannot spell the value at all.
//!   **This is an open DEFECT**, not a licence. Each row names the exact grammar change
//!   that would close it and who owns that decision. The set is asserted EXACTLY, so it
//!   can neither grow silently nor be quietly forgotten once fixed.
//! * [`Exception::CarrierOverlap`] — two categories accept one text as their own
//!   literal. Same status as `NoSurface`: an open defect, enumerated exactly.
//!
//! # Non-vacuity
//!
//! `negative_control_*` proves the corpus reaches every literal category, that the
//! comparison can fail, and that the exception table is not silently absorbing rows that
//! actually pass.

#![cfg(all(feature = "calculator", feature = "rhocalc"))]

use mettail_runtime::{CanonicalBigInt, CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat64};

// ═══════════════════════════════════════════════════════════════════════════
// The exception vocabulary
// ═══════════════════════════════════════════════════════════════════════════

/// Why a `(language, category, value)` row is allowed not to satisfy A1 exactly, or a
/// `(language, text)` row not to satisfy A2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exception {
    /// The pattern excludes a leading `-` BY DESIGN and the category has a unary-minus
    /// rule that reads the detached sign. Denotation-preserving; asserted, not assumed.
    SignIsAnOperator,
    /// ⚠ OPEN DEFECT — the declared pattern has no word for this value.
    NoSurface,
    /// ⚠ OPEN DEFECT — two categories claim one text as their own literal.
    CarrierOverlap,
}

/// One A1 row: what was built, what it displayed as, what came back.
struct Roundtrip {
    language: &'static str,
    category: &'static str,
    built: String,
    surface: String,
    recovered: Result<String, String>,
}

impl Roundtrip {
    fn holds(&self) -> bool {
        matches!(&self.recovered, Ok(got) if got == &self.built)
    }

    fn describe(&self) -> String {
        format!(
            "  {}::{} {} — display {:?} ⇒ {}",
            self.language,
            self.category,
            self.built,
            self.surface,
            match &self.recovered {
                Ok(got) => got.clone(),
                Err(e) => format!("PARSE ERROR: {e}"),
            }
        )
    }
}

/// Build one A1 row. `$cat` must expose `$ctor` and `parse`.
macro_rules! roundtrip {
    ($rows:expr, $language:literal, $cat:ident, $ctor:ident, $($v:expr),+ $(,)?) => {{
        $(
            mettail_runtime::clear_var_cache();
            let lit = $cat::$ctor($v);
            let surface = format!("{}", lit);
            let recovered = match $cat::parse(&surface) {
                Ok(t) => Ok(format!("{t:?}")),
                Err(e) => Err(e),
            };
            $rows.push(Roundtrip {
                language: $language,
                category: stringify!($cat),
                built: format!("{lit:?}"),
                surface,
                recovered,
            });
        )+
    }};
}

fn bigint(n: i64) -> CanonicalBigInt {
    CanonicalBigInt::new(n.into())
}
fn bigrat(numer: i64, denom: i64) -> CanonicalBigRat {
    CanonicalBigRat::try_from_nd(numer.into(), denom.into()).expect("well-formed rational")
}
fn fixed(text: &str) -> CanonicalFixedPoint {
    mettail_runtime::parse_fixed_lit(text).expect("fixed-point literal")
}
fn float(x: f64) -> CanonicalFloat64 {
    CanonicalFloat64::from(x)
}

// ═══════════════════════════════════════════════════════════════════════════
// A1 — every word `Display` writes, the category reads back
// ═══════════════════════════════════════════════════════════════════════════

/// The A1 corpus, swept over every literal category of both languages that declare a
/// `literals { … }` block, plus the implicit-native categories that sit alongside them.
fn a1_rows() -> Vec<Roundtrip> {
    let mut rows = Vec::with_capacity(64);
    {
        use mettail_languages::calculator::{BigInt, BigRat, Bool, Fixed, Float, Int, Str, UInt32};
        roundtrip!(rows, "calc", Int, NumLit, 0i32, 7, -7, i32::MAX, i32::MIN);
        roundtrip!(rows, "calc", UInt32, NumLit, 0u32, 7, u32::MAX);
        roundtrip!(rows, "calc", BigInt, NumLit, bigint(0), bigint(7), bigint(-7), bigint(3_000_000_000));
        roundtrip!(rows, "calc", BigRat, RatLit, bigrat(0, 1), bigrat(7, 1), bigrat(-7, 1), bigrat(3, 4), bigrat(-1, 2));
        roundtrip!(rows, "calc", Fixed, FixedLit, fixed("0p0"), fixed("7p2"), fixed("-260592200p0"));
        roundtrip!(rows, "calc", Float, FloatLit, float(0.0), float(1.5), float(-1.5));
        roundtrip!(rows, "calc", Bool, BoolLit, true, false);
        roundtrip!(rows, "calc", Str, StringLit, String::new(), "ab".to_string());
    }
    {
        use mettail_languages::rhocalc::{BigInt, BigRat, Bool, Fixed, Float, Int, Str, UInt32};
        roundtrip!(rows, "rhocalc", Int, NumLit, 0i64, 7, -7, i64::MAX, i64::MIN);
        roundtrip!(rows, "rhocalc", UInt32, NumLit, 0u32, 7, u32::MAX);
        roundtrip!(rows, "rhocalc", BigInt, NumLit, bigint(0), bigint(7), bigint(-7));
        roundtrip!(rows, "rhocalc", BigRat, RatLit, bigrat(0, 1), bigrat(7, 1), bigrat(-7, 1), bigrat(3, 4), bigrat(-1, 2));
        roundtrip!(rows, "rhocalc", Fixed, FixedLit, fixed("0p0"), fixed("7p2"), fixed("-7p0"));
        roundtrip!(rows, "rhocalc", Float, FloatLit, float(0.0), float(1.5), float(-1.5));
        roundtrip!(rows, "rhocalc", Bool, BoolLit, true, false);
        roundtrip!(rows, "rhocalc", Str, StringLit, String::new(), "ab".to_string());
    }
    rows
}

/// The DECLARED A1 exceptions, keyed by `(language, category, built term)`.
///
/// Each row states the exception kind; the rows tagged [`Exception::NoSurface`] are open
/// grammar defects and are documented individually at the bottom of this file.
fn a1_exception(language: &str, category: &str, built: &str) -> Option<Exception> {
    match (language, category, built) {
        // ── SignIsAnOperator ────────────────────────────────────────────────────
        // Calculator's `Int` pattern carries no `-?` by an explicit merge decision
        // ("unary minus is an operator, not a signed literal" — aligned with Rholang),
        // so `-7` is read as `Neg(NumLit 7)`. Same denotation, same category.
        ("calc", "Int", "NumLit(-7)") => Some(Exception::SignIsAnOperator),
        // Calculator's `BigRat` pattern likewise has no `-?`; `NegBigRat` reads the
        // detached sign. This is the side condition that
        // `macros/src/gen/syntax/display.rs::category_has_unary_minus_rule` now checks
        // against the GRAMMAR instead of assuming it absent.
        ("calc", "BigRat", "RatLit(Ratio { numer: -7, denom: 1 })")
        | ("calc", "BigRat", "RatLit(Ratio { numer: -1, denom: 2 })") => {
            Some(Exception::SignIsAnOperator)
        },

        // ── NoSurface (OPEN DEFECTS — see the ledger at the bottom) ─────────────
        ("calc", "Int", "NumLit(-2147483648)") => Some(Exception::NoSurface),
        ("rhocalc", "BigRat", "RatLit(Ratio { numer: 3, denom: 4 })")
        | ("rhocalc", "BigRat", "RatLit(Ratio { numer: -1, denom: 2 })") => {
            Some(Exception::NoSurface)
        },
        _ => None,
    }
}

#[test]
fn a1_every_word_display_writes_the_category_reads_back() {
    let rows = a1_rows();
    let mut unexpected = Vec::with_capacity(rows.len());
    let mut stale = Vec::with_capacity(8);
    for row in &rows {
        let declared = a1_exception(row.language, row.category, &row.built);
        match (row.holds(), declared) {
            (true, None) => {},
            (false, Some(_)) => {},
            (false, None) => unexpected.push(row.describe()),
            (true, Some(kind)) => stale.push(format!(
                "  {}::{} {} now HOLDS but is still declared {kind:?}",
                row.language, row.category, row.built
            )),
        }
    }
    assert!(
        unexpected.is_empty(),
        "A1: {} literal(s) display a word their own category does not read back, and are \
         NOT in the declared exception table. Either the Display is wrong or the exception \
         is missing a row with its reason:\n{}",
        unexpected.len(),
        unexpected.join("\n"),
    );
    assert!(
        stale.is_empty(),
        "A1: {} declared exception(s) no longer apply — the underlying defect was fixed. \
         REMOVE the row (and its ledger entry) so the table keeps meaning what it says:\n{}",
        stale.len(),
        stale.join("\n"),
    );
}

/// The `SignIsAnOperator` rows are not waved through: each must preserve the DENOTATION
/// and settle to a fixpoint after one parse.
#[test]
fn a1_a_detached_sign_preserves_the_denotation() {
    use mettail_languages::calculator::{BigRat, Int};

    mettail_runtime::clear_var_cache();
    // `Int`: `-7` ⇒ `Neg(NumLit 7)`, which re-displays `-7`.
    let seven = Int::NumLit(-7);
    let surface = format!("{seven}");
    assert_eq!(surface, "-7");
    let back = Int::parse(&surface).expect("`-7` must parse at Int");
    assert_eq!(format!("{back:?}"), "Neg(NumLit(7))", "the sign must be read as the operator");
    assert_eq!(format!("{back}"), surface, "…and re-display to the same surface");

    // `BigRat`: `-7r` ⇒ `NegBigRat(RatLit 7)`; `-1r/2r` ⇒ `NegBigRat(RatLit 1/2)`.
    for (numer, denom, want_surface, want_inner) in [
        (-7i64, 1i64, "-7r", "RatLit(Ratio { numer: 7, denom: 1 })"),
        (-1, 2, "-1r/2r", "RatLit(Ratio { numer: 1, denom: 2 })"),
    ] {
        mettail_runtime::clear_var_cache();
        let lit = BigRat::RatLit(bigrat(numer, denom));
        let surface = format!("{lit}");
        assert_eq!(surface, want_surface, "the negative rational's surface");
        let back = BigRat::parse(&surface).expect("the negative rational must parse");
        assert_eq!(
            format!("{back:?}"),
            format!("NegBigRat({want_inner})"),
            "the sign must be read by `NegBigRat`, keeping the value in the BigRat carrier"
        );
        assert_eq!(format!("{back}"), surface, "…and re-display to the same surface");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// A2 — one numeral, one carrier, chosen by the TEXT
// ═══════════════════════════════════════════════════════════════════════════

/// The texts swept for A2. Every integer spelling either language can lex, plus the
/// non-integer literal forms, so a carrier that reaches outside its own family shows up.
const A2_TEXTS: &[&str] = &[
    "0", "7", "7i32", "7i64", "7u32", "7n", "7r", "3r/4r", "7p0", "7.5", "1e3", "0x1F", "0x1Fu32",
    "3000000000", "4294967296", "-7", "-7n", "-7r", "-7p0", "true", "\"ab\"",
];

fn calculator_literal_carriers(text: &str) -> Vec<&'static str> {
    use mettail_languages::calculator::{BigInt, BigRat, Bool, Fixed, Float, Int, Str, UInt32};
    let mut out = Vec::with_capacity(2);
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
    if matches!(Bool::parse(text), Ok(Bool::BoolLit(_))) {
        out.push("Bool");
    }
    if matches!(Str::parse(text), Ok(Str::StringLit(_))) {
        out.push("Str");
    }
    out
}

fn rhocalc_literal_carriers(text: &str) -> Vec<&'static str> {
    use mettail_languages::rhocalc::{BigInt, BigRat, Bool, Fixed, Float, Int, Str, UInt32};
    let mut out = Vec::with_capacity(2);
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
    if matches!(Bool::parse(text), Ok(Bool::BoolLit(_))) {
        out.push("Bool");
    }
    if matches!(Str::parse(text), Ok(Str::StringLit(_))) {
        out.push("Str");
    }
    out
}

/// ⚠ The DECLARED A2 exceptions — every one an OPEN DEFECT, enumerated exactly.
///
/// RhoCalc's `UInt32` has no `literals { … }` entry, so the macro synthesizes the
/// default acceptor for its native kind
/// (`macros/src/gen/runtime/wpda_codegen/prefix.rs::default_eval_body_for_native_kind`,
/// `parse_int_lit(text, Some(Suffix::U32))`), which admits every UNSUFFIXED integer that
/// fits `u32`. RhoCalc's `Int` pattern already OWNS those spellings — and the `…u32`
/// spelling too, deliberately (`languages/src/rhocalc.rs:196`, divergence I(b)). So each
/// text below has TWO literal carriers, exactly the shape divergence I killed for
/// `BigInt` — and `languages/src/rhocalc.rs:112` asserts in prose that it cannot happen
/// ("`UInt32` has NO literal surface … no election, no context, no parentheses").
fn rhocalc_a2_exception(text: &str) -> Option<Exception> {
    matches!(text, "0" | "7" | "7u32" | "0x1F" | "0x1Fu32" | "3000000000")
        .then_some(Exception::CarrierOverlap)
}

#[test]
fn a2_calculator_gives_every_numeral_exactly_one_carrier() {
    let mut overlaps = Vec::with_capacity(A2_TEXTS.len());
    for text in A2_TEXTS {
        let carriers = calculator_literal_carriers(text);
        if carriers.len() > 1 {
            overlaps.push(format!("  {text:>16} ⇒ {carriers:?}"));
        }
    }
    assert!(
        overlaps.is_empty(),
        "A2: calculator must give every numeral at most ONE literal carrier — the premise \
         that makes its global election unobservable in the surface; {} text(s) overlap:\n{}",
        overlaps.len(),
        overlaps.join("\n"),
    );
}

#[test]
fn a2_rhocalc_overlaps_are_exactly_the_known_int_uint32_set() {
    let mut undeclared = Vec::with_capacity(A2_TEXTS.len());
    let mut stale = Vec::with_capacity(8);
    for text in A2_TEXTS {
        let carriers = rhocalc_literal_carriers(text);
        match (carriers.len() > 1, rhocalc_a2_exception(text)) {
            (true, Some(_)) => assert_eq!(
                carriers,
                vec!["Int", "UInt32"],
                "the declared rhocalc overlap is Int/UInt32; {text:?} overlaps differently: \
                 {carriers:?}"
            ),
            (false, None) => {},
            (true, None) => undeclared.push(format!("  {text:>16} ⇒ {carriers:?}")),
            (false, Some(_)) => stale.push(format!("  {text:>16} no longer overlaps")),
        }
    }
    assert!(
        undeclared.is_empty(),
        "A2: rhocalc grew a NEW literal-carrier overlap beyond the known Int/UInt32 set; \
         {} text(s):\n{}",
        undeclared.len(),
        undeclared.join("\n"),
    );
    assert!(
        stale.is_empty(),
        "A2: {} rhocalc overlap(s) were FIXED — remove them from `rhocalc_a2_exception` and \
         from the ledger so the table keeps meaning what it says:\n{}",
        stale.len(),
        stale.join("\n"),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// NEGATIVE CONTROLS
// ═══════════════════════════════════════════════════════════════════════════

/// NC1 — the A1 corpus really reaches every literal category of both languages. A corpus
/// that silently dropped a category would let its Display drift unwatched.
#[test]
fn negative_control_a1_corpus_covers_every_literal_category() {
    let rows = a1_rows();
    for language in ["calc", "rhocalc"] {
        for category in ["Int", "UInt32", "BigInt", "BigRat", "Fixed", "Float", "Bool", "Str"] {
            assert!(
                rows.iter().any(|r| r.language == language && r.category == category),
                "the A1 corpus does not exercise {language}::{category}"
            );
        }
    }
    // The MEASURED size of the corpus above (2026-07-27). A floor, not a target: it
    // catches a row set that SHRANK, which is how a category quietly stops being swept.
    const A1_CORPUS_SIZE: usize = 53;
    assert!(
        rows.len() >= A1_CORPUS_SIZE,
        "the A1 corpus shrank from its measured {A1_CORPUS_SIZE} rows to {} — a literal \
         value stopped being swept",
        rows.len(),
    );
}

/// NC2 — `Roundtrip::holds` can return false, and the exception table is not absorbing
/// rows that actually pass (that is what the `stale` half of A1 asserts, exercised here
/// on a synthetic row so the machinery itself is proven).
#[test]
fn negative_control_the_a1_comparison_can_fail() {
    let mismatch = Roundtrip {
        language: "synthetic",
        category: "Cat",
        built: "NumLit(7)".to_string(),
        surface: "7".to_string(),
        recovered: Ok("SomethingElse(7)".to_string()),
    };
    assert!(!mismatch.holds(), "a differing term must not count as a round-trip");
    assert!(mismatch.describe().contains("SomethingElse"), "{}", mismatch.describe());

    let unparseable = Roundtrip {
        language: "synthetic",
        category: "Cat",
        built: "NumLit(7)".to_string(),
        surface: "7".to_string(),
        recovered: Err("boom".to_string()),
    };
    assert!(!unparseable.holds(), "an unparseable surface must not count as a round-trip");
    assert!(unparseable.describe().contains("PARSE ERROR"), "{}", unparseable.describe());

    let agrees = Roundtrip {
        language: "synthetic",
        category: "Cat",
        built: "NumLit(7)".to_string(),
        surface: "7".to_string(),
        recovered: Ok("NumLit(7)".to_string()),
    };
    assert!(agrees.holds(), "an identical term must count as a round-trip");
}

/// NC3 — the A2 corpus really is discriminating: it must contain texts that land in
/// several DIFFERENT carriers, or "at most one carrier" would hold by the corpus being
/// too narrow to reach more than one category at all.
#[test]
fn negative_control_a2_corpus_reaches_several_carriers() {
    let mut seen: std::collections::BTreeSet<&'static str> = std::collections::BTreeSet::new();
    for text in A2_TEXTS {
        seen.extend(calculator_literal_carriers(text));
    }
    for expected in ["Int", "UInt32", "BigInt", "BigRat", "Fixed", "Float", "Bool", "Str"] {
        assert!(seen.contains(expected), "the A2 corpus never reaches {expected}: {seen:?}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// ⚠ OPEN-DEFECT LEDGER — the exceptions above, with owners
// ═══════════════════════════════════════════════════════════════════════════
//
// Three defects are enumerated by the tables above rather than fixed, because each needs
// a GRAMMAR decision that is not the display generator's to make. They are listed here so
// the decision is recorded with the evidence, not lost in a commit message.
//
// ── D1 · calculator `Int` has no surface for `i32::MIN` ────────────────────────────
//   Display writes `-2147483648`; the pattern has no `-?`, so the sign must be read by
//   `Neg`, whose operand `2147483648` overflows `i32` and is therefore a `BigInt`. The
//   value has NO surface at `Int`, and `Int::parse` on its own Display fails outright.
//   Reachable by folding (`-2147483647 - 1`) and by a proptest draw of `arb_int`, where
//   it would panic rather than fail cleanly.
//   Closing it = giving calculator's `Int` pattern a `-?`, which reverses the explicit
//   merge decision "No leading `-?`: aligned with main/Rholang (unary minus is an
//   operator, not a signed literal)" and changes how `1-7` lexes.
//   OWNER: the grammar author.
//
// ── D2 · rhocalc `BigRat` has no surface for a composite rational ─────────────────
//   `RatLit 3/4` displays `3/4r` — outside its own `-?(…)r`, and unparseable at
//   `BigRat`. Calculator's twin was fixed by the composite-aware Display arm
//   (`macros/src/gen/syntax/display.rs::composite_repeat_of_optional_group`), which is
//   grammar-derived and fires only where the pattern DECLARES a composite form;
//   rhocalc's does not, so its Display is left where it was rather than emitting a
//   surface its own literal language does not contain.
//   Closing it = giving rhocalc's `BigRat` pattern the composite `(/(…)r)?` group, at
//   which point the same derived arm produces `3r/4r` with no further change. That
//   widens a literal beyond upstream's `bigrat_literal /-?\d+r/`, i.e. a divergence.
//   OWNER: consensus.
//
// ── D3 · rhocalc `UInt32` shares six spellings with `Int` ─────────────────────────
//   See `rhocalc_a2_exception`. `UInt32` has no `literals { … }` entry, so it inherits
//   the synthesized default acceptor, which takes every unsuffixed integer that fits
//   `u32` — the spellings `Int` already owns. Two carriers for one numeral is exactly
//   what divergence I removed for `BigInt`, and `languages/src/rhocalc.rs:112` states in
//   prose that `UInt32` has no literal surface at all.
//   It does NOT break the display fixpoint (both carriers display identically, which is
//   why the round-trip properties pass), but it does make a numeral's carrier
//   context-elected, and rhocalc's operators are carrier-EXACT.
//   Closing it = deciding what `UInt32::NumLit`'s surface IS: either give it a distinct
//   declared one, or remove its literal arm and accept that the constructor has no
//   surface (which the generated `uint32_display_parse_roundtrip` property would then
//   have to stop asserting).
//   OWNER: consensus — rhocalc is the Rholang 1.4 grammar and the carrier of a numeral
//   is observable in `combine_plus`.
