//! ROUND-TRIP INVARIANT — `parse ∘ display = id`.
//!
//! # Why this file exists
//!
//! Two independently-sufficient defects made `display`/`parse` **non-term-preserving**,
//! and the whole pre-existing corpus missed both, because every round-trip assertion in
//! the tree tested **display stability** rather than **term preservation**:
//!
//! ```text
//!     assert_eq!(displayed, format!("{}", parsed));   // ← display STABILITY
//!     assert_eq!(term,      parsed);                  // ← term PRESERVATION (what is needed)
//! ```
//!
//! Term preservation implies display stability; the converse fails whenever `display`
//! maps two distinct terms to one string. A display that does that is perfectly stable
//! and still loses the term. That is exactly what happened, twice.
//!
//! ## Defect 1 — a real constructor used as a bracketing device
//!
//! `macros/src/gen/syntax/display.rs::find_projection_surface_wrapper` rendered a
//! cross-category projection operand at `min_bp > 0` by **borrowing** the first
//! delimited single-base-param rule of the target category and re-emitting that rule's
//! surface around the source term. For a rholang `Proc` operand the election landed on
//! `POutputNil . q:Proc |- "@" "Nil" "!" "(" q ")"` — a **send**:
//!
//! ```text
//!     Add(CastInt 1, CastInt 2)   ─display→  "@Nil!(1) + @Nil!(2)"
//!                                 ─parse──→  Add(POutputNil 1, POutputNil 2)
//! ```
//!
//! Two integers went in; two sends on the null-process channel came out. The bracketing
//! intent was legitimate — a display-transparent projection whose source is an operator
//! term does fuse with the surrounding operator — but a rule of the target category
//! cannot serve as a bracket, because every rule of the target category MEANS something.
//!
//! The replacement is the mechanism the display generator already had one layer down:
//! a cross-category projection forwards `BpLookup::atomic_child_bp(source) =
//! max_bp(source) + 1` to its child, so the SOURCE category's own precedence logic
//! emits the language's pure, inert `(` … `)` grouping — which denotes nothing
//! (`languages/tests/calculator_grouping_is_inert.rs`). Because the threshold is
//! consulted per term, a self-delimiting source emits no parentheses at all.
//!
//! ## Defect 2 — the fixpoint loop checked the wrong invariant
//!
//! `macros/src/gen/mod.rs::parse_structured` started from `parse_via_wpda(input)`
//! (correct) and then, whenever `display(parsed) != input`, replaced the representative
//! with the reparse of its **own display**, accepting as soon as `redisplay == display`.
//! That compares a display against the *previous* display, never against `input`, so the
//! accepted term need not denote the input. It now accepts only on `redisplay == input`.
//!
//! # The invariant pinned here
//!
//! Each case asserts a **triple**, so no leg can be satisfied vacuously by another:
//!
//! | leg | assertion | what it pins |
//! |---|---|---|
//! | S | `display(t) == surface` | the golden surface — moves loudly if display changes |
//! | P | `parse(surface) == t` | the parser recovers the term from that surface |
//! | R | `parse(display(t)) == t` | the round-trip proper |
//!
//! Every case is checked through **both** production parse entry points — `Cat::parse`
//! (which is `parse_structured`, where defect 2 lived) and `Cat::parse_via_wpda` (the
//! raw representative, where defect 1 lived). A single-entry test would have been
//! passed by either fix alone.
//!
//! Structural equality is `format!("{:?}", …)` equality, in preference to the
//! languages' `term_eq`, which is *deliberately* coarser: rholang's `term_eq`
//! canonicalizes every `@`-send sugar
//! (`languages/src/rholang/runtime.rs::normalize_send_sugar_canon`), so `POutputNil(q)`
//! and `POutput(NQuote(PZero), q)` compare EQUAL under it — a term-preservation test
//! must not inherit that coarsening. The corpus is binder-free, which additionally
//! makes `Debug` equality insensitive to variable-cache identity.
//!
//! # Scope — where `parse ∘ display = id` is and is not achievable
//!
//! The invariant is meaningful only where `display` is **injective**. It is not
//! injective across an auto-injected numeric tower: calculator's `IntToBigRat` has no
//! surface of its own, so `AddBigRat(IntToBigRat 1, IntToBigRat 2)` and
//! `IntToBigRat(AddInt(1, 2))` are two distinct terms with one surface, `1 + 2`. No
//! bracketing device can separate them — the language declares them surface-identical.
//! That is a property of the auto-injection lattice, not of this fix, so `BigRat` is
//! covered by [`calculator_bigrat_projection_operand_is_bracketed_not_denoted`], which
//! pins the *bracketing* (the defect-1 property) without claiming injectivity.
//!
//! ## ★ The second non-injective region: SURFACE SYNONYMY (2026-07-26)
//!
//! A grammar may spell one term more than one way, and Rholang's `Name` does:
//! `NQuote(p)` (`@(p)`), `NQuoteShort(p)` (`@p`) and `NQuoteNil` (`@Nil`) are three
//! constructors with one denotation — the last two say so in their own `fold` bodies.
//! Before 2026-07-26 each rendered its OWN surface, which made `Display` a function of
//! the CONSTRUCTOR rather than of the TERM and left `Display ∘ Parse` without a fixpoint:
//! a term whose synonym sat two nesting layers deep shed one surface per layer
//! (`(@(error)) <- @Nil` → `@(error) <- @Nil` → `@error <- @Nil`). `Display` now renders
//! every member of a synonymy class through the class's DECLARED canonical member
//! (`languages/src/rholang.rs`: `NQuoteShort … canonical`), which is what closes that gap.
//!
//! ⚠ **So `display` is DELIBERATELY non-injective on a synonymy class, and LEG R changes
//! shape there.** It does NOT weaken: `parse(display(t))` is still asserted EXACTLY, it is
//! just asserted to be the class's CANONICAL MEMBER rather than `t` itself —
//! `parse(display(NQuote(PZero))) == NQuoteShort(PZero)`, on the nose. Naming the quotient
//! explicitly is strictly stronger than relaxing the comparison to a coarse equality (which
//! is what the header already warns against for `term_eq`). The classes are enumerated and
//! their singleton-after-normalisation property is asserted per language by
//! `languages/tests/surface_synonymy_gate.rs`.
//!
//! # Non-vacuity
//!
//! The `negative_control_*` tests prove the harness can fail: they run the same
//! comparison machinery over deliberately mismatched inputs and assert it reports a
//! mismatch, assert `report` actually panics, and assert the corpus really exercises
//! the operand positions where the defects lived.

#![cfg(all(feature = "rholang", feature = "calculator"))]

use std::sync::Arc;

// ═══════════════════════════════════════════════════════════════════════════
// Harness
// ═══════════════════════════════════════════════════════════════════════════

/// One round-trip observation: what the term is, what it displayed as, and what came
/// back when a surface was parsed.
#[derive(Debug)]
struct Observation {
    case: &'static str,
    entry: &'static str,
    want_surface: &'static str,
    got_surface: String,
    want_term: String,
    /// `Ok(debug)` when the surface parsed, `Err(message)` when it did not.
    got_term: Result<String, String>,
}

impl Observation {
    /// The legs, as failure messages. Empty ⇒ the case holds.
    fn failures(&self) -> Vec<String> {
        // At most one failure per leg: the surface leg and the term leg.
        let mut out = Vec::with_capacity(2);
        if self.got_surface != self.want_surface {
            out.push(format!(
                "[{} / {}] LEG S (golden surface) — display(t) moved\n      want surface: {:?}\n      got  surface: {:?}\n      term        : {}",
                self.case, self.entry, self.want_surface, self.got_surface, self.want_term,
            ));
        }
        match &self.got_term {
            Ok(got) if got == &self.want_term => {},
            Ok(got) => out.push(format!(
                "[{} / {}] LEG R (term preservation) — parse(surface) != t\n      surface: {:?}\n      want   : {}\n      got    : {}",
                self.case, self.entry, self.got_surface, self.want_term, got,
            )),
            Err(err) => out.push(format!(
                "[{} / {}] LEG R (term preservation) — surface does not parse\n      surface: {:?}\n      error  : {}",
                self.case, self.entry, self.got_surface, err,
            )),
        }
        out
    }
}

/// LEGS S + R — display the term, then parse what it displayed.
///
/// The 6-argument form takes the term LEG R must recover, which is `t` itself EXCEPT where
/// `t` belongs to a SURFACE-SYNONYMY class: there `display` is deliberately non-injective and
/// the recovered term is the class's DECLARED CANONICAL MEMBER (see the module header). The
/// comparison stays exact `Debug` equality either way.
macro_rules! observe_roundtrip {
    ($case:expr, $entry:expr, $parse:expr, $term:expr, $surface:expr) => {
        observe_roundtrip!($case, $entry, $parse, $term, $surface, None::<String>)
    };
    ($case:expr, $entry:expr, $parse:expr, $term:expr, $surface:expr, $want_rt:expr) => {{
        mettail_runtime::clear_var_cache();
        let term = $term;
        let want_term: String =
            Option::<String>::from($want_rt).unwrap_or_else(|| format!("{:?}", term));
        let got_surface = format!("{}", term);
        let got_term = match $parse(&got_surface) {
            Ok(p) => Ok(format!("{:?}", p)),
            Err(e) => Err(format!("{:?}", e)),
        };
        Observation {
            case: $case,
            entry: $entry,
            want_surface: $surface,
            got_surface,
            want_term,
            got_term,
        }
    }};
}

/// LEG P — the parser recovers the term from the *golden* surface, not from
/// `display(t)`. This keeps LEG R honest: without it, a display that drifted to some
/// other self-consistent surface would still "round-trip".
macro_rules! observe_from_surface {
    ($case:expr, $entry:expr, $parse:expr, $term:expr, $surface:expr) => {
        observe_from_surface!($case, $entry, $parse, $term, $surface, None::<String>)
    };
    ($case:expr, $entry:expr, $parse:expr, $term:expr, $surface:expr, $want_rt:expr) => {{
        mettail_runtime::clear_var_cache();
        // Where the golden surface is the CANONICAL member's surface, the parser recovers the
        // canonical member — the same quotient LEG R names, for the same reason.
        let want_term: String =
            Option::<String>::from($want_rt).unwrap_or_else(|| format!("{:?}", $term));
        let got_term = match $parse($surface) {
            Ok(p) => Ok(format!("{:?}", p)),
            Err(e) => Err(format!("{:?}", e)),
        };
        Observation {
            case: $case,
            entry: $entry,
            want_surface: $surface,
            got_surface: $surface.to_string(),
            want_term,
            got_term,
        }
    }};
}

/// Run all three legs for one `(case, term, golden surface)` through both production
/// parse entry points, appending five observations to `obs`.
macro_rules! push_all_legs {
    ($obs:expr, $case:expr, $parse:path, $wpda:path, $term:expr, $surface:expr) => {
        push_all_legs!($obs, $case, $parse, $wpda, $term, $surface, None::<String>)
    };
    ($obs:expr, $case:expr, $parse:path, $wpda:path, $term:expr, $surface:expr, $want_rt:expr) => {{
        $obs.push(observe_roundtrip!($case, "parse (S+R)", $parse, $term, $surface, $want_rt));
        $obs.push(observe_roundtrip!(
            $case,
            "parse_via_wpda (S+R)",
            $wpda,
            $term,
            $surface,
            $want_rt
        ));
        $obs.push(observe_from_surface!($case, "parse (P)", $parse, $term, $surface, $want_rt));
        $obs.push(observe_from_surface!(
            $case,
            "parse_via_wpda (P)",
            $wpda,
            $term,
            $surface,
            $want_rt
        ));
    }};
}

fn report(observations: Vec<Observation>) {
    let mut failures: Vec<String> = Vec::with_capacity(observations.len());
    for o in &observations {
        failures.extend(o.failures());
    }
    assert!(
        failures.is_empty(),
        "\n{} of {} round-trip observations failed:\n\n{}\n",
        failures.len(),
        observations.len(),
        failures.join("\n\n"),
    );
}

mod rho {
    pub use mettail_languages::rholang::{Int, Name, Proc};
}
mod calc {
    pub use mettail_languages::calculator::{BigInt, BigRat, Bool, Int, UInt32};
}

fn rho_int(v: i64) -> rho::Proc {
    rho::Proc::CastInt(Arc::new(rho::Int::NumLit(v)))
}

// ═══════════════════════════════════════════════════════════════════════════
// rholang — Proc (the category the defects were found in)
// ═══════════════════════════════════════════════════════════════════════════

/// `(name, term, golden surface)`.
///
/// The arithmetic and relational rows are the direct defect-1 witnesses: each has a
/// cross-category projection (`CastInt : Int ▸ Proc`) in an operand slot whose inherited
/// `min_bp` is non-zero — exactly the position that used to borrow `POutputNil`'s
/// `@Nil!( … )` surface. Their goldens carry NO parentheses, because a bare integer
/// literal is self-delimiting and cannot fuse with `+`; rholang's `Int` category has no
/// operators of its own, so no rholang projection operand ever needs a bracket. The
/// `@Nil!(1)` row is the control that keeps the send surface reachable: a term that
/// really IS a send must still display as one.
fn rho_proc_cases() -> Vec<(&'static str, rho::Proc, &'static str)> {
    vec![
        ("proc/zero", rho::Proc::PZero, "Nil"),
        ("proc/int-atom", rho_int(1), "1"),
        ("proc/add", rho::Proc::Add(Arc::new(rho_int(1)), Arc::new(rho_int(2))), "1 + 2"),
        ("proc/sub", rho::Proc::Sub(Arc::new(rho_int(3)), Arc::new(rho_int(4))), "3 - 4"),
        ("proc/mul", rho::Proc::Mul(Arc::new(rho_int(5)), Arc::new(rho_int(6))), "5 * 6"),
        ("proc/eq", rho::Proc::Eq(Arc::new(rho_int(7)), Arc::new(rho_int(8))), "7 == 8"),
        ("proc/lt", rho::Proc::Lt(Arc::new(rho_int(9)), Arc::new(rho_int(10))), "9 < 10"),
        (
            "proc/add-nested-left",
            rho::Proc::Add(
                Arc::new(rho::Proc::Add(Arc::new(rho_int(1)), Arc::new(rho_int(2)))),
                Arc::new(rho_int(3)),
            ),
            "1 + 2 + 3",
        ),
        (
            "proc/add-zero-operand",
            rho::Proc::Add(Arc::new(rho::Proc::PZero), Arc::new(rho_int(1))),
            "Nil + 1",
        ),
        (
            "proc/par-infix",
            rho::Proc::PParInfix(Arc::new(rho_int(1)), Arc::new(rho_int(2))),
            "1 | 2",
        ),
        ("proc/send-nil-channel", rho::Proc::POutputNil(Arc::new(rho_int(1))), "@Nil!(1)"),
    ]
}

#[test]
fn rholang_proc_display_parse_preserves_terms() {
    let cases = rho_proc_cases();
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface) in cases {
        push_all_legs!(
            obs,
            case,
            rho::Proc::parse,
            rho::Proc::parse_via_wpda,
            term.clone(),
            surface
        );
    }
    report(obs);
}

// ═══════════════════════════════════════════════════════════════════════════
// rholang — Name and Int
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn rholang_name_display_parse_preserves_terms() {
    // ★ SURFACE SYNONYMY (2026-07-26). `Name`'s `{ NQuote, NQuoteShort, NQuoteNil }` is a
    // synonymy class, so `Display` renders all three through the class's DECLARED canonical
    // member `NQuoteShort` (`languages/src/rholang.rs`). Two things follow, and both are
    // asserted rather than excused:
    //
    //   LEG S — the golden surface of an `NQuote` is now the SHORTHAND. `@(Nil)` ⇒ `@Nil`,
    //           `@(4)` ⇒ `@4`. It is not merely shorter: it is the surface official Rholang
    //           writes, and it is the one `InputBindQuoted . pat:Proc |- "@" pat "<-" n`
    //           already spelled, which is WHY it is the canonical member.
    //   LEG R — `parse(display(t))` recovers the CANONICAL member, `NQuoteShort(p)`, not the
    //           `NQuote(p)` we started from. Still exact `Debug` equality; the quotient is
    //           named in the expectation instead of hidden in a coarser comparison.
    //
    //   name/quote-add is the CONTROL: `Add` binds looser than `NQuoteShort`'s declared
    //   `prefix(220)`, so Display's own precedence test re-emits the parentheses and the
    //   surface stays `@(1 + 2)` — which re-parses to `NQuote`, not to `NQuoteShort`. It shows
    //   the canonicalisation is a PRECEDENCE-CORRECT re-rendering rather than a blanket
    //   bracket deletion.
    let quote_zero_canonical = format!("{:?}", rho::Name::NQuoteShort(Arc::new(rho::Proc::PZero)));
    let quote_int_canonical = format!("{:?}", rho::Name::NQuoteShort(Arc::new(rho_int(4))));
    let cases: Vec<(&'static str, rho::Name, &'static str, Option<String>)> = vec![
        (
            "name/quote-zero",
            rho::Name::NQuote(Arc::new(rho::Proc::PZero)),
            "@Nil",
            Some(quote_zero_canonical),
        ),
        (
            "name/quote-int",
            rho::Name::NQuote(Arc::new(rho_int(4))),
            "@4",
            Some(quote_int_canonical),
        ),
        // A whole cross-category sum inside a quote: the parentheses come from the canonical
        // member's `prefix(220)` threshold (`Add` binds looser), so this case round-trips to
        // `NQuote` itself and needs no quotient.
        (
            "name/quote-add",
            rho::Name::NQuote(Arc::new(rho::Proc::Add(Arc::new(rho_int(1)), Arc::new(rho_int(2))))),
            "@(1 + 2)",
            None,
        ),
    ];
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface, want_rt) in cases {
        push_all_legs!(
            obs,
            case,
            rho::Name::parse,
            rho::Name::parse_via_wpda,
            term.clone(),
            surface,
            want_rt.clone()
        );
    }
    report(obs);
}

#[test]
fn rholang_int_display_parse_preserves_terms() {
    let cases: Vec<(&'static str, rho::Int, &'static str)> =
        vec![("int/lit", rho::Int::NumLit(42), "42")];
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface) in cases {
        push_all_legs!(obs, case, rho::Int::parse, rho::Int::parse_via_wpda, term.clone(), surface);
    }
    report(obs);
}

// ═══════════════════════════════════════════════════════════════════════════
// calculator — Int / BigInt / Bool / UInt32
//
// A DIFFERENT language, whose projection-surface election landed on `bigrat( … )` /
// `bigint( … )` rather than rholang's `@Nil!( … )`. `UInt32` carries the positive
// bracketing witness.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn calculator_int_display_parse_preserves_terms() {
    let cases: Vec<(&'static str, calc::Int, &'static str)> = vec![
        ("calc-int/lit", calc::Int::NumLit(7), "7"),
        (
            "calc-int/add",
            calc::Int::AddInt(Arc::new(calc::Int::NumLit(1)), Arc::new(calc::Int::NumLit(2))),
            "1 + 2",
        ),
    ];
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface) in cases {
        push_all_legs!(
            obs,
            case,
            calc::Int::parse,
            calc::Int::parse_via_wpda,
            term.clone(),
            surface
        );
    }
    report(obs);
}

#[test]
fn calculator_bigint_display_parse_preserves_terms() {
    let cases: Vec<(&'static str, calc::BigInt, &'static str)> = vec![(
        "calc-bigint/lit",
        calc::BigInt::NumLit(mettail_runtime::CanonicalBigInt::new(5i64.into())),
        "5n",
    )];
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface) in cases {
        push_all_legs!(
            obs,
            case,
            calc::BigInt::parse,
            calc::BigInt::parse_via_wpda,
            term.clone(),
            surface
        );
    }
    report(obs);
}

#[test]
fn calculator_bool_display_parse_preserves_terms() {
    let cases: Vec<(&'static str, calc::Bool, &'static str)> =
        vec![("calc-bool/lit-true", calc::Bool::BoolLit(true), "true")];
    let mut obs = Vec::with_capacity(cases.len() * 4);
    for (case, term, surface) in cases {
        push_all_legs!(
            obs,
            case,
            calc::Bool::parse,
            calc::Bool::parse_via_wpda,
            term.clone(),
            surface
        );
    }
    report(obs);
}

/// ★ THE POSITIVE BRACKETING WITNESS.
///
/// `BoolToUInt32 : Bool ▸ UInt32` is an AUTO-INJECTED projection with no surface of its
/// own, and `Bool` HAS operators (`LtEqInt . a:Int, b:Int |- a "<=" b : Bool`). So a
/// `Bool`-rooted operand of a `UInt32` operator is exactly the shape defect 1 mishandled
/// AND one where a bracket is genuinely required: bare, `1 <= 2 bitand 3u32` would let
/// `bitand` capture `2`.
///
/// The replacement mechanism supplies that bracket from the SOURCE category's own
/// precedence logic at `atomic_child_bp(Bool)`, so the surface is
/// `(1 <= 2) bitand 3u32` — a pure grouping, denoting nothing — and the term comes back
/// exactly. The bare row underneath pins the other half: at `min_bp == 0` the same
/// projection emits NO parentheses, which is unchanged from before the fix.
#[test]
fn calculator_uint32_projection_operand_brackets_and_round_trips() {
    let bracketed = calc::UInt32::BitAndUInt32(
        Arc::new(calc::UInt32::BoolToUInt32(Arc::new(calc::Bool::LtEqInt(
            Arc::new(calc::Int::NumLit(1)),
            Arc::new(calc::Int::NumLit(2)),
        )))),
        Arc::new(calc::UInt32::NumLit(3)),
    );
    let bare = calc::UInt32::BoolToUInt32(Arc::new(calc::Bool::LtEqInt(
        Arc::new(calc::Int::NumLit(1)),
        Arc::new(calc::Int::NumLit(2)),
    )));

    let mut obs = Vec::with_capacity(8);
    push_all_legs!(
        obs,
        "calc-u32/projection-operand-bracketed",
        calc::UInt32::parse,
        calc::UInt32::parse_via_wpda,
        bracketed.clone(),
        "(1 <= 2) bitand 3u32"
    );
    push_all_legs!(
        obs,
        "calc-u32/projection-at-top-level-bare",
        calc::UInt32::parse,
        calc::UInt32::parse_via_wpda,
        bare.clone(),
        "1 <= 2"
    );
    report(obs);

    // The bracket must be the language's pure grouping, not a borrowed constructor.
    let surface = format!("{}", bracketed);
    assert!(
        surface.starts_with("(1 <= 2)"),
        "the projection operand must be grouped: {surface:?}"
    );
    for borrowed in ["bigint(", "bigrat(", "uint(", "int(", "float(", "fixed("] {
        assert!(
            !surface.contains(borrowed),
            "the bracket must denote nothing, but the surface borrows {borrowed:?}: {surface:?}"
        );
    }
}

/// calculator's `BigRat` — the defect-1 PROPERTY, without an injectivity claim.
///
/// `IntToBigRat : Int ▸ BigRat` is auto-injected and surface-less, so
/// `AddBigRat(IntToBigRat 1, IntToBigRat 2)` and `IntToBigRat(AddInt(1, 2))` are two
/// distinct terms sharing the surface `1 + 2`. No display can separate them; the
/// language declares them surface-identical. So this case pins what the fix is
/// responsible for — the operand is **bracketed** rather than **denoted** — and does
/// not assert a round-trip that the auto-injection lattice makes impossible.
///
/// Before the fix the surface was `bigrat(1 + 2) + error`, which reparsed as a
/// `BigratCast` over `Proc` — a real constructor the term never contained.
#[test]
fn calculator_bigrat_projection_operand_is_bracketed_not_denoted() {
    mettail_runtime::clear_var_cache();
    let term = calc::BigRat::AddBigRat(
        Arc::new(calc::BigRat::IntToBigRat(Arc::new(calc::Int::AddInt(
            Arc::new(calc::Int::NumLit(1)),
            Arc::new(calc::Int::NumLit(2)),
        )))),
        Arc::new(calc::BigRat::Err),
    );
    let surface = format!("{}", term);
    assert_eq!(
        surface, "(1 + 2) + error",
        "the Int-rooted projection operand must be grouped by the pure `(` … `)` form"
    );
    assert!(
        !surface.contains("bigrat("),
        "the operand must not borrow the `BigratCast` constructor: {surface:?}"
    );

    // The bracket is load-bearing: dropping it changes the reading. Without the group,
    // `1 + 2 + error` associates entirely at `BigRat`, losing the `Int`-level sum.
    let grouped = calc::BigRat::parse(&surface).expect("the grouped surface must parse");
    let ungrouped = calc::BigRat::parse("1 + 2 + error").expect("the bare surface must parse");
    assert_ne!(
        format!("{grouped:?}"),
        format!("{ungrouped:?}"),
        "if the group were inert here the fix would be pinning nothing"
    );
    // …and the Int-level sum survives inside the group.
    assert!(
        format!("{grouped:?}").contains("AddInt(NumLit(1), NumLit(2))"),
        "the grouped reading must keep the Int-level sum: {grouped:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// NEGATIVE CONTROLS — the harness must be able to FAIL
// ═══════════════════════════════════════════════════════════════════════════

/// NC1 — the comparison machinery reports a real mismatch.
///
/// Feeds `Observation` a term/surface pair that is deliberately wrong on both legs and
/// asserts BOTH fire. Without this, a bug that made `failures()` always return an empty
/// vector would leave every test above passing vacuously.
#[test]
fn negative_control_harness_detects_mismatch() {
    let bogus = Observation {
        case: "nc1",
        entry: "synthetic",
        want_surface: "1 + 2",
        got_surface: "@Nil!(1) + @Nil!(2)".to_string(),
        want_term: "Add(CastInt(NumLit(1)), CastInt(NumLit(2)))".to_string(),
        got_term: Ok(
            "Add(POutputNil(CastInt(NumLit(1))), POutputNil(CastInt(NumLit(2))))".to_string()
        ),
    };
    let failures = bogus.failures();
    assert_eq!(
        failures.len(),
        2,
        "the harness must report BOTH a moved surface and a lost term: {failures:#?}"
    );
    assert!(failures[0].contains("LEG S"), "{failures:#?}");
    assert!(failures[1].contains("LEG R"), "{failures:#?}");

    let unparseable = Observation {
        case: "nc1b",
        entry: "synthetic",
        want_surface: "1 + 2",
        got_surface: "1 + 2".to_string(),
        want_term: "Add(…)".to_string(),
        got_term: Err("ParseFailed".to_string()),
    };
    let failures = unparseable.failures();
    assert_eq!(failures.len(), 1, "a non-parsing surface is one LEG R failure: {failures:#?}");
    assert!(failures[0].contains("does not parse"), "{failures:#?}");
}

/// NC2 — `report` actually panics on a failing observation.
#[test]
#[should_panic(expected = "round-trip observations failed")]
fn negative_control_report_panics_on_failure() {
    report(vec![Observation {
        case: "nc2",
        entry: "synthetic",
        want_surface: "a",
        got_surface: "b".to_string(),
        want_term: "A".to_string(),
        got_term: Ok("A".to_string()),
    }]);
}

/// NC3 — the corpus is not trivial: it must actually exercise the operand position where
/// defect 1 lived (a cross-category projection under a non-zero `min_bp`). A corpus of
/// only atoms would pass every assertion above without touching that path at all.
#[test]
fn negative_control_corpus_exercises_projection_operands() {
    let cases = rho_proc_cases();
    assert!(cases.len() >= 8, "corpus too small to be meaningful: {}", cases.len());

    // Golden surfaces carrying a binary infix operator — the slots with non-zero
    // inherited `min_bp`.
    let infix: Vec<&str> = cases
        .iter()
        .map(|(_, _, s)| *s)
        .filter(|s| {
            [" + ", " - ", " * ", " == ", " < ", " | "]
                .iter()
                .any(|op| s.contains(op))
        })
        .collect();
    assert!(
        infix.len() >= 6,
        "the corpus must exercise several infix operand positions, got {infix:?}"
    );

    // At least one of those operands must be a CROSS-CATEGORY projection
    // (`CastInt : Int ▸ Proc`) — the exact shape that borrowed `POutputNil`'s surface.
    let projection_operand = cases.iter().any(|(name, term, _)| {
        *name == "proc/add"
            && matches!(term, rho::Proc::Add(a, b)
                if matches!(**a, rho::Proc::CastInt(_)) && matches!(**b, rho::Proc::CastInt(_)))
    });
    assert!(
        projection_operand,
        "the corpus must contain a cross-category projection operand"
    );

    // …and the corpus must also contain a term that legitimately IS a send, so a fix
    // that simply suppressed every `@Nil!( … )` surface would be caught.
    let real_send = cases.iter().any(|(_, term, surface)| {
        matches!(term, rho::Proc::POutputNil(_)) && *surface == "@Nil!(1)"
    });
    assert!(
        real_send,
        "the corpus must keep a genuine send, so the send surface stays reachable"
    );
}

/// NC4 — the specific historical regression, stated on its own so the failure message
/// names the defect rather than diffing two ASTs. `POutputNil` is a **send**; it must
/// never appear in the surface of a term that contains no send.
#[test]
fn negative_control_projection_operand_does_not_borrow_a_send() {
    mettail_runtime::clear_var_cache();
    let term = rho::Proc::Add(Arc::new(rho_int(1)), Arc::new(rho_int(2)));
    let displayed = format!("{}", term);
    assert!(
        !displayed.contains("@Nil!"),
        "a sum of two integers must not display as a pair of sends: {displayed:?}"
    );
    assert!(
        !displayed.contains('!'),
        "a sum of two integers must not display any send sigil: {displayed:?}"
    );
    assert_eq!(displayed, "1 + 2");
}

/// NC5 — defect 2, stated directly on the entry point that carried it.
/// `Proc::parse` is `parse_structured`; for this input it used to return the reparse of
/// its own display and hand back two sends.
#[test]
fn negative_control_parse_structured_returns_the_input_s_term() {
    mettail_runtime::clear_var_cache();
    let parsed = rho::Proc::parse("1 + 2").expect("`1 + 2` must parse");
    assert_eq!(
        format!("{parsed:?}"),
        "Add(CastInt(NumLit(1)), CastInt(NumLit(2)))",
        "parse_structured must return the input's term, not the reparse of a display"
    );
}
