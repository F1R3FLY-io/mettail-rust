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
//! ★ **`NoSurface` is now UNINHABITED.** Its two rows — D1 and D2 in the ledger at the
//! bottom of this file — were fixed in the grammars on 2026-07-27 and left the table by
//! being FIXED, never by being reclassified. The variant is retained so that a new
//! violation is TYPED rather than shrugged at.
//!
//! ★ **`CarrierOverlap` still has its six rows (D3), and the ledger now records a
//! REFUTATION as well as the defect**: the obvious repair — give `UInt32` the `…u32`
//! spelling, as calculator does — was implemented, measured, and REJECTED because it
//! changes a value f1r3node computes differently (`bitnot 0u32`). What remains is not a
//! grammar change.
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
///
/// `NoSurface` is RETAINED WITH NO INHABITANTS (2026-07-27): both its rows were fixed in
/// the grammars. Keeping the variant means the next violation is classified by a name that
/// already says "this is a defect" instead of being argued about in a review. It is
/// `dead_code` only in the sense that the codebase currently has no defect of that shape —
/// which is the point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exception {
    /// The pattern excludes a leading `-` BY DESIGN and the category has a unary-minus
    /// rule that reads the detached sign. Denotation-preserving; asserted, not assumed.
    SignIsAnOperator,
    /// ⚠ OPEN DEFECT — the declared pattern has no word for this value.
    /// Uninhabited since 2026-07-27 (ledger D1, D2).
    #[allow(dead_code)]
    NoSurface,
    /// ⚠ OPEN DEFECT — two categories claim one text as their own literal.
    /// Six inhabitants (ledger D3).
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
        // Calculator's `BigRat` pattern has no `-?`; `NegBigRat` reads the detached sign.
        // This is the side condition that
        // `macros/src/gen/syntax/display.rs::category_has_unary_minus_rule` now checks
        // against the GRAMMAR instead of assuming it absent.
        //
        // ⚠ Calculator's `Int` row is GONE, and its absence is the D1 fix, not an
        // oversight: the pattern now carries `-?`, so `-7` is the LITERAL `NumLit(-7)`
        // and A1 holds exactly. `a1_a_detached_sign_preserves_the_denotation` lost its
        // `Int` half for the same reason, and `d1_calculator_int_spells_its_whole_domain`
        // pins what replaced it.
        ("calc", "BigRat", "RatLit(Ratio { numer: -7, denom: 1 })")
        | ("calc", "BigRat", "RatLit(Ratio { numer: -1, denom: 2 })") => {
            Some(Exception::SignIsAnOperator)
        },

        // ── NoSurface — NO ROWS. D1 (`calc::Int` at `i32::MIN`) and D2 (`rhocalc::BigRat`
        //    at a composite rational) were the only two, and both were FIXED in the
        //    grammar on 2026-07-27; see the ledger at the bottom of this file.
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
///
/// ⚠ **This test lost its `Int` half on 2026-07-27, and the reason matters.** It used to
/// open by asserting `Int::parse("-7") = Neg(NumLit(7))` — the calculator `Int` row of
/// `a1_exception`. That row existed ONLY because calculator's `Int` pattern had no `-?`,
/// which is exactly the defect D1 fixed. Had the half been left in place it would have
/// been asserting the defect, so it moved WITH its row rather than being carried over as
/// a control that no longer controls anything. What replaced it is
/// [`d1_calculator_int_spells_its_whole_domain`], which asserts the stronger property the
/// fix bought: the sign is part of the literal, so no denotation has to be RECOVERED.
#[test]
fn a1_a_detached_sign_preserves_the_denotation() {
    use mettail_languages::calculator::BigRat;

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
// THE THREE CLOSED DEFECTS — one pinning test each (ledger D1 · D2 · D3)
// ═══════════════════════════════════════════════════════════════════════════

/// **D1 CLOSED.** Calculator's `Int` pattern carries `-?`, so the category can spell every
/// inhabitant of its declared domain `![i32]` — `i32::MIN` included.
///
/// Before the fix `Display` wrote `-2147483648` and `Int::parse` on that very word FAILED
/// (`no realizable readings`), because the sign had to be read by `Neg` and the operand
/// `2147483648` overflows `i32`. A proptest draw of `arb_int` therefore PANICKED rather
/// than failing cleanly.
///
/// The three assertions are the three things the reversal had to be checked against:
/// the value that motivated it, the reading it changes, and the reading it must NOT change
/// (`1-7` is still subtraction — the one-token `1`,`-7` fork is two adjacent `Int`s and
/// dies on feasibility, which is the mechanism `languages/src/rhocalc.rs`'s divergence
/// I(b) note describes).
#[test]
fn d1_calculator_int_spells_its_whole_domain() {
    use mettail_languages::calculator::Int;

    // (1) The value that has no operator form: its own Display now parses, at `Int`.
    mettail_runtime::clear_var_cache();
    let min = Int::NumLit(i32::MIN);
    let surface = format!("{min}");
    assert_eq!(surface, "-2147483648");
    let back = Int::parse(&surface).expect("`i32::MIN` must parse at Int from its own Display");
    assert_eq!(format!("{back:?}"), "NumLit(-2147483648)", "and come back as the same literal");
    assert_eq!(format!("{back}"), surface, "…and re-display to the same surface");

    // (2) An ordinary negative is now the LITERAL, not a recovered denotation.
    mettail_runtime::clear_var_cache();
    let neg = Int::parse("-7").expect("`-7` must parse at Int");
    assert_eq!(format!("{neg:?}"), "NumLit(-7)", "the sign is part of the numeral token");

    // (3) What must NOT move: sign-abutted subtraction, spaced and unspaced.
    for (source, want) in
        [("1-7", "SubInt(NumLit(1), NumLit(7))"), ("1 -7", "SubInt(NumLit(1), NumLit(7))")]
    {
        mettail_runtime::clear_var_cache();
        let term = Int::parse(source).unwrap_or_else(|e| panic!("{source:?} must parse: {e}"));
        assert_eq!(
            format!("{term:?}"),
            want,
            "{source:?} must still be subtraction: the one-token reading is two adjacent \
             processes and dies on feasibility, so `Minus` wins"
        );
    }
}

/// **D2 CLOSED.** RhoCalc's `BigRat` pattern carries the composite `(/(…)r)?` group, so a
/// rational with a denominator ≠ 1 — which `Div`'s fold PRODUCES — has a literal surface.
///
/// The measured exposure before the fix was unparseability, NOT the value corruption its
/// calculator twin had: the broken word was `3/4r`, which keeps the right operand in the
/// rational carrier, so `BigRat::parse` gave a hard parse error rather than silently
/// becoming integer division. Both halves are pinned here, along with the boundary that
/// bounds the divergence: only the UNSPACED spelling is claimed.
#[test]
fn d2_rhocalc_bigrat_spells_a_composite_rational() {
    use mettail_languages::rhocalc::{BigRat, Proc};

    for (numer, denom, want_surface) in
        [(3i64, 4i64, "3r/4r"), (-1, 2, "-1r/2r"), (7, 1, "7r"), (-7, 1, "-7r")]
    {
        mettail_runtime::clear_var_cache();
        let lit = BigRat::RatLit(bigrat(numer, denom));
        let surface = format!("{lit}");
        assert_eq!(surface, want_surface, "the tail belongs to each COMPONENT of the composite");
        let back = BigRat::parse(&surface)
            .unwrap_or_else(|e| panic!("{surface:?} must parse at BigRat: {e}"));
        assert_eq!(format!("{back:?}"), format!("{lit:?}"), "and come back as the same literal");
        assert_eq!(format!("{back}"), surface, "…and re-display to the same surface");
    }

    // The divergence is bounded by whitespace: any space defeats maximal munch, so a
    // DIVISION term keeps its own surface and its own reading.
    mettail_runtime::clear_var_cache();
    let one_token = Proc::parse("3r/4r").expect("the unspaced spelling is one literal token");
    assert_eq!(format!("{one_token:?}"), "CastBigRat(RatLit(Ratio { numer: 3, denom: 4 }))");
    mettail_runtime::clear_var_cache();
    let spaced = Proc::parse("3r / 4r").expect("the spaced spelling is a division");
    assert_eq!(
        format!("{spaced:?}"),
        "Div(CastBigRat(RatLit(Ratio { numer: 3, denom: 1 })), \
         CastBigRat(RatLit(Ratio { numer: 4, denom: 1 })))"
    );
    assert_eq!(
        format!("{spaced}"),
        "3r / 4r",
        "`Div` displays the SPACED form, so no division term's surface is stolen by the literal"
    );
}

/// **D3 STILL OPEN — this test pins the REFUTATION of its obvious repair**, so the repair
/// is not tried a second time and so the refutation cannot rot silently.
///
/// The repair was: give `UInt32` the `…u32` spelling (exactly as `languages/src/
/// calculator.rs` does) and take it off `Int`. It was implemented and measured on
/// 2026-07-27, and it moves a VALUE. `normalize_ground` maps
/// `UnsignedIntLiteral{bits ≤ 64, ≤ i64::MAX}` to `GInt`, so the `u32` suffix is a
/// SPELLING of a 64-bit integer, not a 32-bit carrier —
///
/// ```text
///     bitnot 0u32          ⇒ -1            ← f1r3node, and RhoCalc today
///     bitnot 0u32          ⇒ 4294967295    ← with the spelling moved to `UInt32`
///     bitnot uint(0, 32)   ⇒ 4294967295    ← the MeTTaIL-only 32-bit carrier, either way
/// ```
///
/// — so `…u32` must stay at `Int`. Every OTHER Rholang numeral spelling is `Int`'s too, by
/// the same table, which leaves `UInt32` no spelling it may own; the remaining repair is to
/// give a `UInt32` value the surface of the cast that PRODUCES it (`uint(v, 32)`), and that
/// is a `Display` codegen change rather than a grammar one.
///
/// (`rhocalc_tests::numeral_carrier_is_context_independent::u32_suffix_is_an_i64_literal`
/// pins the reduction; this pins the LITERAL-LAYER premise it rests on, in the file whose
/// exception table would otherwise invite the repair.)
#[test]
fn d3_rhocalc_u32_suffix_must_remain_an_int_literal() {
    use mettail_languages::rhocalc::{Int, UInt32};

    for text in ["7u32", "0x1Fu32", "0u32"] {
        mettail_runtime::clear_var_cache();
        assert!(
            matches!(Int::parse(text), Ok(Int::NumLit(_))),
            "{text:?} must be an `Int` literal: `normalize_ground` maps the `u32` suffix to \
             `GInt`, so moving it to `UInt32` would make `bitnot 0u32` answer 4294967295 \
             where f1r3node answers -1"
        );
    }
    // The overlap that makes D3 a defect, asserted from the other side so this test also
    // fails if the defect is fixed some OTHER way and the ledger is not updated.
    mettail_runtime::clear_var_cache();
    assert!(
        matches!(UInt32::parse("7u32"), Ok(UInt32::NumLit(_))),
        "D3 is still open: `UInt32`'s synthesized acceptor still takes `7u32` as well"
    );
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
/// spelling too, deliberately (divergence I(b) in `languages/src/rhocalc.rs`). So each
/// text below has TWO literal carriers, exactly the shape divergence I killed for
/// `BigInt`.
///
/// ★ **Do not close this by moving `…u32` to `UInt32`.** That was tried and REFUTED on
/// 2026-07-27 — see [`d3_rhocalc_u32_suffix_must_remain_an_int_literal`] and ledger D3.
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
///
/// ★ The rhocalc half was ADDED on 2026-07-27. Until then the control covered calculator
/// only, so the rhocalc sweep had no non-vacuity guard of its own: a corpus that stopped
/// reaching (say) `Fixed` or `BigRat` at rhocalc would have made
/// `a2_rhocalc_overlaps_are_exactly_the_known_int_uint32_set` quieter without making it
/// wrong, and D3's exception table is asserted EXACTLY, so a shrinking corpus is precisely
/// how its six rows could appear to close without anything being fixed.
#[test]
fn negative_control_a2_corpus_reaches_several_carriers() {
    for (language, carriers_of) in [
        ("calc", calculator_literal_carriers as fn(&str) -> Vec<&'static str>),
        ("rhocalc", rhocalc_literal_carriers as fn(&str) -> Vec<&'static str>),
    ] {
        let mut seen: std::collections::BTreeSet<&'static str> = std::collections::BTreeSet::new();
        for text in A2_TEXTS {
            seen.extend(carriers_of(text));
        }
        for expected in ["Int", "UInt32", "BigInt", "BigRat", "Fixed", "Float", "Bool", "Str"] {
            assert!(
                seen.contains(expected),
                "the A2 corpus never reaches {language}::{expected}: {seen:?}"
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// DEFECT LEDGER — D1 ✔ CLOSED · D2 ✔ CLOSED · D3 ⚠ OPEN (its obvious repair REFUTED)
// ═══════════════════════════════════════════════════════════════════════════
//
// Three defects were enumerated by the tables above rather than fixed, because each needed
// a GRAMMAR decision. All three were RULED ON on 2026-07-27; two were fixed in the
// grammars, and the third was found not to be a grammar defect at all. The rulings and
// their evidence are recorded here so a future reader can see WHY, not merely THAT.
//
// The exception set is now: two `SignIsAnOperator` rows (calculator's `BigRat`), and six
// `CarrierOverlap` rows (D3). `NoSurface` is uninhabited.
//
// ── D1 · calculator `Int` had no surface for `i32::MIN` ─── CLOSED ────────────────
//   SYMPTOM (measured). `Display` wrote `-2147483648`; the pattern had no `-?`, so the
//   sign had to be read by `Neg`, whose operand `2147483648` overflows `i32`.
//   `Int::parse("-2147483648")` returned `Err(no realizable readings)` — a literal whose
//   own Display did not parse — and an `arb_int` draw PANICKED on it.
//   RULING: the pattern was wrong, not the value. `i32::MIN` is an inhabitant of the
//   DECLARED domain `![i32] as Int`, reachable by folding (`-2147483647 - 1`) as well as
//   by generation. The competing direction — "the value is outside the category's domain,
//   fix it at construction" — would have to narrow `![i32]` to `i32 ∖ {MIN}`: a refinement
//   type the DSL does not have, a fallible derived constructor, and still an unparseable
//   `Display` for a value any consumer can build directly. So: `-?` in the pattern.
//   THE PRIOR DECISION, ENGAGED. This REVERSES "No leading `-?`: aligned with
//   main/Rholang (unary minus is an operator, not a signed literal) — merge decision
//   'prefer main's regexes'" (`cc21ee1b`). The reversal attacks the decision's PREMISE:
//   Rholang's own grammar puts the sign inside the token (`long_literal /-?\d+/`,
//   `signed_int_literal /-?\d+i[1-9]\d*/`; only `unsigned_int_literal` has no sign), so
//   "aligned with Rholang" argues FOR the `-?`, not against it. RhoCalc — the grammar that
//   IS Rholang 1.4 — had already been corrected on exactly this ground (divergence I(b),
//   `12704fc1`), which is why its `i64::MIN` row in the A1 corpus above has never needed
//   an exception. Calculator was the last holdout of a refuted premise.
//   FIX: `languages/src/calculator.rs`, `Int` pattern gains `-?`. Pinned by
//   `d1_calculator_int_spells_its_whole_domain`.
//
// ── D2 · rhocalc `BigRat` had no surface for a composite rational ─── CLOSED ──────
//   SYMPTOM (measured). `RatLit 3/4` displayed `3/4r` — the tail appended once to
//   `CanonicalBigRat`'s own `3/4` rendering — and `BigRat::parse("3/4r")` was a hard
//   parse error. The value is produced by `Div`'s fold (`3r / 4r`) and drawn by
//   `arb_bigrat`, so it is not hypothetical.
//   EXPOSURE, ESTABLISHED: unparseability ONLY, not value corruption. Calculator's twin
//   defect DID corrupt values (`RatLit 3/4` displayed `3/4`, re-parsed as integer division
//   `IntToBigRat(DivInt 3 4)`, evaluated to `0`). RhoCalc cannot reach that: its broken
//   word keeps the `r` on the right operand, so the rational carrier is forced and no
//   integer division is expressible. Fail-closed, not silently wrong.
//   RULING: the pattern was wrong. At the `BigRat` CATEGORY there is no operator that
//   could read a detached `/` — RhoCalc sites division at `Proc` — so unlike the detached
//   SIGN there is no operator form for `Display` to fall back on, and A1 is satisfiable
//   only by a literal spelling.
//   THE DIVERGENCE, STATED. Upstream's `bigrat_literal` is `/-?\d+r/`; the composite is a
//   deliberate widening, recorded as divergence I(d) in `languages/src/rhocalc.rs`. It is
//   FORCED by a real asymmetry — MeTTaIL folds and therefore PRODUCES composite rationals;
//   f1r3node folds nothing and never has to print one — and it is bounded: it claims only
//   the UNSPACED `Nr/Dr`, the three-token reading folds to the same value, `Div` displays
//   the SPACED form so no term's surface is stolen, and the fork stays in the lattice.
//   FIX: `languages/src/rhocalc.rs`, `BigRat` pattern gains `(/(…)r)?`; the derived
//   composite-aware `Display` arm then writes `3r/4r` with no codegen change. Pinned by
//   `d2_rhocalc_bigrat_spells_a_composite_rational`.
//
// ── D3 · rhocalc `UInt32` shares six spellings with `Int` ─── ⚠ OPEN ──────────────
//   SYMPTOM (measured). `UInt32` has no `literals { … }` entry, so it inherits the
//   SYNTHESIZED default acceptor (`parse_int_lit(text, Some(Suffix::U32))`), which takes
//   every unsuffixed integer fitting `u32` — spellings `Int` already owns, plus `…u32`,
//   which `Int` owns deliberately. Six texts, two literal carriers each. It does NOT break
//   the display fixpoint (both carriers display identically), but it makes a numeral's
//   carrier context-elected, and the two carriers do not agree: `3000000000 + 3000000000`
//   is `6000000000` at `Int` and a `u32` overflow `error` at `UInt32`.
//
//   WHICH IS WRONG, THE PROSE OR THE CODE? BOTH, in different clauses, and the correction
//   that ships is the prose. `languages/src/rhocalc.rs` asserted "`UInt32` has NO literal
//   surface … no election, no context, no parentheses". As a description of the CODE that
//   was false — the synthesized acceptor is a literal surface, and a very wide one — so the
//   prose has been corrected in place to say what is actually true and to name D3.
//
//   ★ THE OBVIOUS REPAIR IS REFUTED. Give `UInt32` the `…u32` spelling and take it off
//   `Int` — the shape `languages/src/calculator.rs` uses, and the shape the calculator fix
//   `4aa64cb6` established. It was IMPLEMENTED and MEASURED on 2026-07-27, and it moves a
//   VALUE:
//
//       bitnot 0u32          ⇒ -1            ← f1r3node, and RhoCalc today
//       bitnot 0u32          ⇒ 4294967295    ← with the spelling moved to `UInt32`
//
//   because `normalize_ground` maps `UnsignedIntLiteral{bits ≤ 64, ≤ i64::MAX}` to `GInt`:
//   the `u32` SUFFIX IS A SPELLING OF A 64-BIT INTEGER, not a 32-bit carrier. RhoCalc
//   already pins this (`rhocalc_tests::numeral_carrier_is_context_independent::
//   u32_suffix_is_an_i64_literal`), and `d3_rhocalc_u32_suffix_must_remain_an_int_literal`
//   in this file now pins the literal-layer premise so the repair is not tried again.
//   NOTE the defect is therefore NOT identical to calculator's: calculator's `UInt32` had a
//   `pattern` with a mandatory `u32` tail and an `eval` WIDER than it — a pattern/eval
//   disagreement inside one category. RhoCalc's has no pattern at all, and the spelling its
//   pattern would want belongs to another category by conformance. The precedent does not
//   transfer.
//
//   WHY NOTHING ELSE AT THIS LAYER WORKS. Every Rholang numeral spelling — bare, radix,
//   `…i32`, `…i64`, `…u32` — maps to `GInt` and is therefore `Int`'s, which leaves `UInt32`
//   no spelling it may own. The other minimal move, making `UInt32`'s eval accept NOTHING,
//   closes A2 but breaks A1: `uint(x, 32)` folds to a `UInt32::NumLit`, `Display` writes it
//   (`bitnot uint(0, 32)` displays `4294967295`), and a `NoSurface` row would replace the
//   `CarrierOverlap` rows — a reclassification, not a fix — while also breaking the
//   generated `gen_rhocalc_prop::uint32_display_parse_roundtrip`.
//
//   WHAT WOULD ACTUALLY CLOSE IT. A `UInt32` value's surface must be the cast that PRODUCES
//   it — `uint(v, 32)` — so that it is re-readable AT the 32-bit carrier and collides with
//   no numeral. `NumLit`'s `Display` is derived from the literal pattern, so this is a
//   change in `macros/src/gen/syntax/display.rs` (choose a rule-derived surface for a
//   literal constructor whose category declares no literal domain), plus the regenerated
//   `languages/tests/gen_rhocalc_prop.rs`. Both files are owned elsewhere at the time of
//   writing, so D3 is REPORTED rather than half-fixed.
//   OWNER: the display-codegen owner, jointly with consensus — `uint(v, 32)` as the printed
//   normal form of a 32-bit value is a surface-language change.
