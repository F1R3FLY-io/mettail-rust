//! **THE ARITHMETIC CARRIER MATRIX — every binary operator, at every numeric carrier, MEASURED.**
//!
//! # Why this is measured and not read
//!
//! Work item #115 was filed as *"`BigRat` has no binary `-`; `UInt32` has no `-`, `*`, or `/`"*.
//! Reading the fold bodies REFUTES that as stated: `Sub`, `Mul` and `Div` each carry a
//! `(Proc::CastUInt32(a), Proc::CastUInt32(b))` arm and a `(Proc::CastBigRat(a),
//! Proc::CastBigRat(b))` arm in `languages/src/rholang.rs`. A static read of the arms is therefore
//! not what the filing was about — and neither is it what a user experiences.
//!
//! What a user experiences is the composition of THREE things:
//!
//! 1. which carrier a numeral's TEXT lexes to (divergence I: `Int` owns every ≤64-bit spelling,
//!    `…u32` included, so `7u32` is an `Int` and a `UInt32` value is reachable only through the
//!    MeTTaIL-only cast `uint(v, 32)`);
//! 2. whether the operator has a homogeneous arm at that carrier;
//! 3. what the PROMOTION LATTICE supplies when it does not — auto-injection emits lossless
//!    widening projections (`ast/src/language/model.rs`, the lossless-edge table), so an operator
//!    with no arm at carrier `C` may still answer by widening both operands to some `D ⊃ C`.
//!
//! Only (2) is visible in the fold bodies. (1) and (3) are what make a cell behave, and a cell can
//! be *silently wrong* while its arm is present. This file measures the composition, so the
//! reported gap is the one a program actually hits.
//!
//! # THE MEASURED RESULT (2026-07-30) — the filing's four cells all WORK
//!
//! 78 cells (13 operators × 6 carriers). **74 answer in their own carrier.** The four that do not
//! are NOT the four that were filed:
//!
//! | cell | mettail | upstream floor | verdict |
//! |---|---|---|---|
//! | `6r % 3r` | `error` | **`0`** — `combine_mod`'s `GBigRat` arm, `reduce.rs:3435` | **GAP ⇒ DECLARED** |
//! | `6.0 % 3.0` | `error` | **`Err("Modulus not defined on floating point")`** — `:3425` | already AGREES; pinned |
//! | `6.0 bitand 3.0` | `error` | **none** — upstream has no bitwise operators at all | RULED `error` |
//! | `6.0 bitor 3.0` | `error` | **none** | RULED `error` |
//!
//! And the four cells the filing named — `BigRat -`, `UInt32 -`, `UInt32 *`, `UInt32 /` — every one
//! computes and preserves its carrier (`6r - 3r ⇒ 3r`, `uint(6,32) - uint(3,32) ⇒ 3` in `UInt32`,
//! and likewise for `*` and `/`). The premise is REFUTED by measurement, not by argument.
//!
//! ## The two rulings, and why they are not defaults
//!
//! **`Float %` is not a gap.** Upstream refuses float modulo *explicitly*, with a message
//! (`"Modulus not defined on floating point"`). Declaring it here would be a DIVERGENCE dressed as
//! completeness. ⚠ Note this is the one place the IEEE-754 disposition does NOT extend: the owner
//! ruled that float `÷0` answers IEEE-754 (measured below: `1.0/0.0 ⇒ inf`, `-1.0/0.0 ⇒ -inf`,
//! `0.0/0.0 ⇒ NaN`) and IEEE 754-2019 §5.3.1 does define a `remainder` operation — but upstream
//! declines it, and upstream is the floor on SEMANTICS. Following IEEE here would move a value.
//!
//! **`Float bitand` / `Float bitor` stay `error`, and that is a ruling, not an omission.** Upstream
//! has NO bitwise operators anywhere (derived: zero occurrences of `bitand`/`bitor`/`bitnot` in
//! `f1r3node-rust-mettail`, and none in the consensus tree-sitter grammar), so these are
//! MeTTaIL-only and the disposition is entirely ours. A bitwise operation on an IEEE-754 float has
//! no arithmetic reading; the only implementable one masks the bit PATTERN, which is not a function
//! of the represented VALUE — `0.0` and `-0.0` are equal floats with different patterns — so it
//! would break the property every other arm has, that the answer depends only on operand values.
//! Failing closed is the correct answer, not a missing one.
//!
//! ## ⚠ TWO DERIVED DIVERGENCES ON `Fixed` — ONE NOW REPAIRED, ONE STILL OPEN
//!
//! Both were found by this matrix. Neither is a missing operator.
//!
//! 1. **`%` had a different DEFINITION — ★ REPAIRED 2026-07-30 by owner ruling ("align `%`
//!    semantics with upstream Rholang"). `Fixed %` now AGREES with upstream.**
//!    `CanonicalFixedPoint::checked_rem` computes the remainder on the aligned unscaled integers
//!    at the shared scale, which is upstream's `combine_mod` `GFixedPoint` arm verbatim
//!    (`reduce.rs:3460-3470`). `7.00p2 % 3.00p2` is `1.00p2` in both; `7.50p2 % 2.00p2` is
//!    `1.50p2` in both.
//!
//!    ⚠ The superseded finding is quoted here so it is not rediscovered and "fixed" back:
//!
//!    > computes `a − trunc_p(a/b)·b` — the remainder after dividing to `p` places … It is NOT an
//!    > arithmetic slip: mettail's `checked_rem` is the matched pair of its `checked_div` (which
//!    > also divides to `p` places) and the two satisfy `q·b + r = a` … Adopting upstream's `%`
//!    > requires re-deciding `/` in the same breath.
//!
//!    Two things in that were wrong. (a) `a − trunc_p(a/b)·b` expands to `(a/b − trunc_p(a/b))·b
//!    = ε·b` with `0 ≤ ε < 10⁻ᵖ` — the division's own TRUNCATION ERROR scaled by the divisor,
//!    bounded by `|b|·10⁻ᵖ` and therefore tending to zero as precision grows. A residual, not a
//!    remainder. (b) `/` did NOT have to be re-decided: `q·b + r = a` is a theorem about the
//!    TRUNCATED INTEGER quotient (C99 §6.5.5), not about a `p`-places quotient, so `/` was never
//!    implicated. `checked_div` is unchanged and `10p1 / 3p1` is still `3.3p1`.
//!
//!    ⚠⚠ **RE-DERIVED 2026-07-30 (work item #200).** This item used to close with a third
//!    argument, verbatim:
//!
//!    > What the finding missed entirely is decisive: the old `%` read `places`, which
//!    > `PartialEq`/`Hash`/`to_canonical_bytes` all declare meaningless (they key on the reduced
//!    > rational), so `7.00p2 == 7.0p1` while `%` answered `0.01` and `0.1` — not a function on
//!    > the type's own equivalence classes.
//!
//!    That argument is DEAD: `places` is now part of `Fixed` identity, `7.00p2 != 7.0p1`, and a
//!    `places`-reading `%` WOULD be a function on the new equivalence classes. Read unamended it
//!    is an argument for restoring the residual-valued `%`. What condemns the old `%` instead is
//!    simpler and is a floor obligation rather than an internal-consistency one: upstream's
//!    `combine_mod` `GFixedPoint` arm (`reduce.rs:3460-3470`) is `&ua % &ub` on the unscaled
//!    integers at `fp1.scale`, and upstream requires equal scales, so at equal scales this `%`
//!    IS upstream's `%`. The residual agreed with it at no scale — `7.50p2 % 2.00p2` returned
//!    `0p0` where upstream returns `1.50p2`. `runtime`'s
//!    `remainder_is_invariant_under_the_places_spelling` remains the guard, re-derived alongside.
//! 2. **Mixed scales are ACCEPTED — STILL OPEN, not changed.** Upstream requires equal scales for
//!    every fixed-point arithmetic operator and raises `OperatorExpectedError { op, expected:
//!    "FixedPoint(p{fp1.scale})", other_type: "FixedPoint(p{fp2.scale})" }` otherwise
//!    (`combine_mod:3446-3452`, `combine_plus:3540`); mettail's `align_pair` aligns to
//!    `max(places)`, so `7.00p2 + 3.000p3` is `10.000p3` here and `7.00p2 % 3.000p3` answers here.
//!    Pre-existing and PERMISSIVE. Adopting the refusal REMOVES ACCEPTED PROGRAMS, which is a
//!    separate ruling from the arithmetic one; the ruling received covered the arithmetic only.
//!
//! Row 1 is now pinned as an AGREEING cell with upstream's answer written down; row 2 remains
//! pinned as KNOWN-DIVERGENT, so neither can be quietly forgotten or mistaken for the other.
//!
//! # The gate
//!
//! The matrix is a DERIVED cross product — the operator list × the carrier list — not a
//! hand-written list of cells. Adding a carrier or an operator to either axis extends it
//! automatically, so a new hole cannot be introduced silently. The four non-preserving cells are
//! declared in `RULED_NON_PRESERVING` with the RULING for each, so a cell that starts or stops
//! preserving its carrier fails the gate either way.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::{
    Proc, RholangLanguage, RholangTerm, RholangTermInner,
};
use mettail_runtime::Language;

const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

/// A numeric carrier, with the surface that PRODUCES a value of it.
///
/// ⚠ `UInt32`'s producer is the CAST, not a literal suffix. Divergence I established that `…u32`
/// is a spelling of a `GInt` upstream (`bitnot 0u32` is `-1`, not `4294967295`), so `Int` owns it
/// and `UInt32` owns no numeral spelling at all.
struct Carrier {
    name: &'static str,
    /// A surface producing the value 6 in this carrier.
    six: &'static str,
    /// A surface producing the value 3 in this carrier.
    three: &'static str,
}

const CARRIERS: &[Carrier] = &[
    Carrier { name: "Int", six: "6", three: "3" },
    Carrier { name: "UInt32", six: "uint(6, 32)", three: "uint(3, 32)" },
    Carrier { name: "BigInt", six: "6n", three: "3n" },
    Carrier { name: "BigRat", six: "6r", three: "3r" },
    Carrier { name: "Fixed", six: "6.00p2", three: "3.00p2" },
    Carrier { name: "Float", six: "6.0", three: "3.0" },
];

/// A binary operator and whether its result should stay in the operand carrier.
struct Operator {
    /// The infix surface.
    surface: &'static str,
    /// `true` for arithmetic (result is a number in the operand carrier); `false` for a
    /// comparison (result is a `Bool` at every carrier).
    arithmetic: bool,
}

const OPERATORS: &[Operator] = &[
    Operator { surface: "+", arithmetic: true },
    Operator { surface: "-", arithmetic: true },
    Operator { surface: "*", arithmetic: true },
    Operator { surface: "/", arithmetic: true },
    Operator { surface: "%", arithmetic: true },
    Operator { surface: "bitand", arithmetic: true },
    Operator { surface: "bitor", arithmetic: true },
    Operator { surface: "==", arithmetic: false },
    Operator { surface: "!=", arithmetic: false },
    Operator { surface: "<", arithmetic: false },
    Operator { surface: ">", arithmetic: false },
    Operator { surface: "<=", arithmetic: false },
    Operator { surface: ">=", arithmetic: false },
];

/// The CARRIER of a folded result, as a short name, or `"error"` / `"stuck:<shape>"`.
fn carrier_of(term: &Proc) -> String {
    match term {
        Proc::CastInt(_) => "Int".to_string(),
        Proc::CastUInt32(_) => "UInt32".to_string(),
        Proc::CastBigInt(_) => "BigInt".to_string(),
        Proc::CastBigRat(_) => "BigRat".to_string(),
        Proc::CastFixed(_) => "Fixed".to_string(),
        Proc::CastFloat(_) => "Float".to_string(),
        Proc::CastBool(_) => "Bool".to_string(),
        Proc::Err => "error".to_string(),
        other => format!("stuck:{}", term_head(other)),
    }
}

fn term_head(term: &Proc) -> &'static str {
    match term {
        Proc::Add(..) => "Add",
        Proc::Sub(..) => "Sub",
        Proc::Mul(..) => "Mul",
        Proc::Div(..) => "Div",
        Proc::Mod(..) => "Mod",
        Proc::BitAnd(..) => "BitAnd",
        Proc::BitOr(..) => "BitOr",
        Proc::Eq(..) => "Eq",
        Proc::Ne(..) => "Ne",
        Proc::Lt(..) => "Lt",
        Proc::Gt(..) => "Gt",
        Proc::LtEq(..) => "LtEq",
        Proc::GtEq(..) => "GtEq",
        _ => "other",
    }
}

/// Fold a source through the host (dovetail) lane, or report the failure as a pseudo-carrier so
/// the matrix has a cell for every combination rather than a panic.
fn fold_carrier_and_value(src: &str) -> (String, String) {
    mettail_runtime::clear_var_cache();
    let parsed = match Proc::parse(src) {
        Ok(p) => p,
        Err(_) => return ("PARSE-FAIL".to_string(), String::new()),
    };
    let term = RholangTerm(RholangTermInner::Proc(parsed));
    match RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES) {
        Ok(normal) => match normal
            .as_any()
            .downcast_ref::<RholangTerm>()
            .map(|t| &t.0)
        {
            Some(RholangTermInner::Proc(p)) => (carrier_of(p), format!("{p}")),
            _ => ("NON-PROC".to_string(), String::new()),
        },
        Err(_) => ("FOLD-FAIL".to_string(), String::new()),
    }
}

/// ★ THE DERIVED MATRIX. Prints the full operator × carrier table (visible with
/// `--nocapture`) and asserts the one invariant that is not a matter of taste: an arithmetic
/// operator applied to two operands of carrier `C` must answer in `C`, and a comparison must
/// answer `Bool`.
///
/// # Why CARRIER PRESERVATION is the right invariant
///
/// Both this grammar's operators and the consensus reducer's `combine_*` family are
/// carrier-EXACT: `combine_plus` has one arm per `ExprInstance` pair and no promotion. So a cell
/// that answers in a WIDER carrier than its operands is not "helpfully lenient" — it is a
/// divergence that changes a value's TYPE, and every downstream carrier-exact operator then sees
/// an operand it has no arm for. A silent promotion is strictly worse than a missing operator,
/// because a missing operator fails closed.
#[test]
fn every_arithmetic_operator_preserves_its_operand_carrier() {
    let mut rows: Vec<String> = Vec::with_capacity(OPERATORS.len() * CARRIERS.len());
    let mut violations: Vec<String> = Vec::new();

    for op in OPERATORS {
        for carrier in CARRIERS {
            let src = format!("{} {} {}", carrier.six, op.surface, carrier.three);
            let (got, rendered) = fold_carrier_and_value(&src);
            let want = if op.arithmetic { carrier.name } else { "Bool" };
            let verdict = if got == want { "ok" } else { "★" };
            rows.push(format!(
                "  {verdict} {:<28} ⇒ {:<10} {}",
                src, got, rendered
            ));
            if got != want {
                violations.push(format!(
                    "  {src:<28} answered {got:<10} (want {want:<8}) value {rendered}"
                ));
            }
        }
    }

    // The matrix is printed unconditionally so a reader can re-derive it without editing code.
    println!("── the arithmetic carrier matrix ({} cells) ──", rows.len());
    for row in &rows {
        println!("{row}");
    }

    // ── the vacuity floor ────────────────────────────────────────────────────────────────
    assert_eq!(
        rows.len(),
        OPERATORS.len() * CARRIERS.len(),
        "the matrix must be the FULL cross product; a short matrix would pass by not looking",
    );
    assert!(
        rows.iter().filter(|r| r.starts_with("  ok")).count() > 0,
        "no cell at all answered in its own carrier — the harness itself is broken, not the \
         grammar",
    );

    // ── the RULED exceptions, checked in BOTH directions ─────────────────────────────────
    //
    // A cell that stops preserving its carrier fails (a regression); a cell listed here that
    // STARTS preserving it also fails, because that means someone declared an operator whose
    // absence was a ruling. Neither direction can drift silently.
    let mut unexpected: Vec<String> = Vec::new();
    for violation in &violations {
        if !RULED_NON_PRESERVING
            .iter()
            .any(|ruled| violation.trim_start().starts_with(ruled.cell))
        {
            unexpected.push(violation.clone());
        }
    }
    assert!(
        unexpected.is_empty(),
        "{} of {} cells do not preserve their operand carrier and are NOT among the ruled \
         exceptions:\n{}\n\n\
         ★ Both this grammar's operators and the consensus reducer's `combine_*` family are \
         carrier-EXACT, so a wider answer is a DIVERGENCE that changes a value's type, and every \
         downstream operator then sees an operand it has no arm for. A missing operator fails \
         closed; a silent promotion does not.",
        unexpected.len(),
        rows.len(),
        unexpected.join("\n"),
    );
    for ruled in RULED_NON_PRESERVING {
        assert!(
            violations
                .iter()
                .any(|v| v.trim_start().starts_with(ruled.cell)),
            "`{}` now PRESERVES its carrier, but its non-preservation was a RULING: {}\n\
             If that ruling has changed, change it here and say so; do not let it drift.",
            ruled.cell,
            ruled.ruling,
        );
    }
}

/// A cell that deliberately does NOT answer in its operand carrier, with the ruling.
struct RuledCell {
    cell: &'static str,
    ruling: &'static str,
}

/// ★ THE FOUR RULED CELLS. Every one answers the `error` term, and for each the reason is written
/// down rather than implied. See the module header for the full argument and the upstream sites.
const RULED_NON_PRESERVING: &[RuledCell] = &[
    RuledCell {
        cell: "6.0 %",
        ruling: "upstream REFUSES float modulo explicitly — `combine_mod`'s `GDouble` arm                  (`reduce.rs:3425`) is `Err(\"Modulus not defined on floating point\")`. Declaring                  it here would be a divergence dressed as completeness. Note this is the one                  place the IEEE-754 disposition does not extend, even though IEEE 754-2019                  §5.3.1 defines `remainder`.",
    },
    RuledCell {
        cell: "6.0 bitand",
        ruling: "MeTTaIL-only operator (upstream has NO bitwise operators anywhere), and a                  bitwise op on an IEEE-754 float has no arithmetic reading: the only                  implementable one masks the bit PATTERN, which is not a function of the                  represented VALUE (`0.0` and `-0.0` are equal with different patterns).",
    },
    RuledCell {
        cell: "6.0 bitor",
        ruling: "as `bitand` — same argument, same ruling.",
    },
    // ⚠ `6.00p2 %` is DELIBERATELY NOT LISTED. It PRESERVES its carrier — it answers a `Fixed` —
    // so it is not a non-preserving cell at all. Its divergence is in the VALUE, which a carrier
    // matrix cannot see, and it is pinned separately by
    // `the_two_fixed_point_divergences_are_pinned_with_upstreams_answer`. Listing it here would
    // conflate two different kinds of defect and would make this table's bidirectional check
    // fail for the wrong reason.
];

// ══════════════════════════════════════════════════════════════════════════════════════════
// The named edge cells — the IEEE ruling, the ÷0 dispositions, and the two Fixed divergences
// ══════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE OWNER'S IEEE-754 RULING, MEASURED. Float division by zero answers IEEE-754 rather than
/// the `error` term, matching upstream's `combine_div` `GDouble` arm.
#[test]
fn float_division_by_zero_answers_ieee_754() {
    for (src, want) in [("1.0 / 0.0", "inf"), ("-1.0 / 0.0", "-inf"), ("0.0 / 0.0", "NaN")] {
        let (carrier, value) = fold_carrier_and_value(src);
        assert_eq!(carrier, "Float", "`{src}` must stay in the Float carrier, not become `error`");
        assert_eq!(value, want, "`{src}` must answer IEEE-754 `{want}`");
    }
}

/// ⚠ DIVISION AND MODULO BY ZERO FAIL CLOSED AT EVERY EXACT CARRIER — the complement of the IEEE
/// row above. `Int`, `UInt32`, `BigInt`, `BigRat` and `Fixed` are exact, so there is no
/// representable answer and the `error` term is the only correct one.
#[test]
fn modulo_and_division_by_zero_fail_closed_at_the_exact_carriers() {
    for src in [
        "7 % 0",
        "uint(7, 32) % uint(0, 32)",
        "7n % 0n",
        "7r % 0r",
        "7.00p2 % 0.00p2",
        "7 / 0",
        "7n / 0n",
        "7r / 0r",
        "7.00p2 / 0.00p2",
    ] {
        let (carrier, _) = fold_carrier_and_value(src);
        assert_eq!(carrier, "error", "`{src}` must fail closed at an exact carrier");
    }
}

/// ★ #115's DECLARED OPERATOR. `BigRat %` answers the rational ZERO for any non-zero divisor,
/// reproducing upstream's `combine_mod` `GBigRat` arm (`reduce.rs:3435-3444`). Not an
/// approximation: in the field ℚ every non-zero `b` divides every `a` exactly, so the remainder is
/// identically 0.
#[test]
fn bigrat_modulo_is_the_rational_zero() {
    for src in ["6r % 3r", "7r % 3r", "1r/2r % 3r", "-7r % 3r"] {
        let (carrier, value) = fold_carrier_and_value(src);
        assert_eq!(
            (carrier.as_str(), value.as_str()),
            ("BigRat", "0r"),
            "`{src}` must be the rational zero, as upstream's `GBigRat` modulo arm is",
        );
    }
}

/// ★ `Fixed %` NOW AGREES WITH UPSTREAM (owner ruling, 2026-07-30) — pinned against UPSTREAM'S
/// value, which is the whole point of the row: the assertion is no longer "this is what we do",
/// it is "this is what upstream does, and we do it too".
///
/// ⚠ Every expected value below was `0.01p2` / `0p0` before the repair — the division's truncation
/// residual `ε·b`, `0 ≤ ε < 10⁻ᵖ`. See the module header for the superseded finding, quoted, and
/// for the two ways it was wrong. Do not move this row back.
#[test]
fn fixed_point_modulo_agrees_with_upstream() {
    // Remainder on the aligned unscaled integers, scale preserved — `reduce.rs:3460-3470`.
    for (src, upstream, derivation) in [
        ("7.00p2 % 3.00p2", "1.00p2", "700 % 300 = 100 at p2"),
        ("7.50p2 % 2.00p2", "1.50p2", "750 % 200 = 150 at p2"),
        // ★ The exactly-divisible case, which is where the old formula was most visibly wrong: it
        // answered `0` here because `7.50/2.50 = 3.00` is exact at two places, and it ALSO answers
        // `0` correctly — so this row only distinguishes the two definitions together with the
        // rows above. Kept because a remainder of zero must survive normalization to `0p0`.
        ("7.50p2 % 2.50p2", "0p0", "750 % 250 = 0, and true zero normalizes to p0"),
        // Sign follows the DIVIDEND (truncated toward zero), as `BigInt`'s and upstream's `GInt`
        // `lhs % rhs` both do.
        ("-7.00p2 % 3.00p2", "-1.00p2", "-700 % 300 = -100 at p2"),
        ("7.00p2 % -3.00p2", "1.00p2", "700 % -300 = 100 at p2"),
    ] {
        let (carrier, value) = fold_carrier_and_value(src);
        assert_eq!(
            (carrier.as_str(), value.as_str()),
            ("Fixed", upstream),
            "`{src}` must answer upstream's `{upstream}` ({derivation}). If this row moves, `%` \
             has drifted off upstream — it is not free to change.",
        );
    }

    // ★ SCALE INVARIANCE OF THE NUMBER, at the SURFACE level. `7.00p2`, `7.0p1` and `7p0` are
    // three spellings of the number seven, so `%` must answer the number one for all three. The
    // superseded `%` gave `0.01p2` and `0.1p1` — three different NUMBERS for one division. The
    // runtime-level guard is
    // `canonical_fixed_point.rs::remainder_is_invariant_under_the_places_spelling`; this is the
    // same law measured through the parser and the fold, where a user meets it.
    let (_, p2) = fold_carrier_and_value("7.00p2 % 3.00p2");
    let (_, p1) = fold_carrier_and_value("7.0p1 % 3.0p1");
    let (_, p0) = fold_carrier_and_value("7p0 % 3p0");
    assert_eq!(
        (p2.as_str(), p1.as_str(), p0.as_str()),
        ("1.00p2", "1.0p1", "1p0"),
        "the three spellings of `7 % 3` must all be the NUMBER one, differing only in how many \
         trailing zeros the scale prints",
    );
    // ⚠⚠ RE-DERIVED 2026-07-30 (work item #200) — THIS LOOP INVERTED. It asserted
    // `("Bool", "true")` with the justification:
    //
    //   > `{lhs} == {rhs}` must be true — `places` is not part of a `Fixed` value's identity,
    //   > so an operation answering different VALUES for different spellings (as `%` did) is
    //   > not a function on this type's equivalence classes
    //
    // `places` IS part of identity now, so the three spellings are three distinct VALUES and
    // `==` answers `false`. ★ That is not a regression: upstream's `combine_eq`
    // (`reduce.rs:3733-3749`) is structural `Par` equality over `GFixedPoint { unscaled, scale }`
    // and has always answered `false` here, so this row moves mettail INTO agreement with the
    // floor rather than away from it.
    //
    // The law the loop above still measures is untouched: `%` answers the same NUMBER for all
    // three spellings. What changed is only that "same number" is no longer spelled `==`.
    // Asserted on the RESULTS' own surfaces rather than on a compound `a % b == c % d`
    // expression, so this row measures the equality law and not `%`-versus-`==` precedence.
    for (lhs, rhs) in [(&p2, &p1), (&p1, &p0)] {
        let (carrier, value) = fold_carrier_and_value(&format!("{lhs} == {rhs}"));
        assert_eq!(
            (carrier.as_str(), value.as_str()),
            ("Bool", "false"),
            "`{lhs} == {rhs}` must be FALSE — `Fixed` identity is the raw `(unscaled, places)` \
             pair since work item #200, and these are two different pairs denoting one number. \
             Upstream answers `false` too",
        );
    }
}

/// ⚠ THE REMAINING `Fixed` DIVERGENCE, PINNED WITH UPSTREAM'S ANSWER WRITTEN DOWN. Mixed scales
/// are ACCEPTED here and REFUSED upstream. Not repaired: adopting the refusal REMOVES ACCEPTED
/// PROGRAMS, a separate owner ruling from the `%` arithmetic one. This row exists so that if it
/// changes, it changes DELIBERATELY.
#[test]
fn mixed_scale_fixed_point_is_accepted_here_and_refused_upstream() {
    // Upstream: `OperatorExpectedError { op: "+", expected: "FixedPoint(p2)",
    //                                   other_type: "FixedPoint(p3)" }` — `combine_plus:3540`.
    let (carrier, value) = fold_carrier_and_value("7.00p2 + 3.000p3");
    assert_eq!(
        (carrier.as_str(), value.as_str()),
        ("Fixed", "10.000p3"),
        "mixed-scale fixed-point addition aligns to `max(places)` here, while upstream raises          `OperatorExpectedError` (`combine_plus:3540`). PERMISSIVE and pre-existing.",
    );
    // ★ The same permissiveness on `%` specifically, which the repair did NOT touch: upstream's
    // `combine_mod:3446-3452` refuses this outright. `7.00p2 % 3.000p3` aligns to p3 —
    // `7000 % 3000 = 1000` — and answers `1.000p3`.
    let (carrier, value) = fold_carrier_and_value("7.00p2 % 3.000p3");
    assert_eq!(
        (carrier.as_str(), value.as_str()),
        ("Fixed", "1.000p3"),
        "mixed-scale `%` answers here (aligned to `max(places)`) while upstream raises \
         `OperatorExpectedError {{ op: \"%\", expected: \"FixedPoint(p2)\", other_type: \
         \"FixedPoint(p3)\" }}` (`combine_mod:3446-3452`). ACCEPTED-PROGRAMS divergence, still \
         open — the `%` ruling covered the arithmetic only.",
    );
}
