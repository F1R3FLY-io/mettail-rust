//! R-D A1 AmbiguityBudget pins (task #18, 2026-07-15).
//!
//! The PURE canonical-GLL engine (the SOLE engine after #19b physically removed
//! the classic lever, 2026-07-15) enforces `AmbiguityBudget(n)` as the count of
//! DISTINCT REALIZED TERMS the goal admits (`|R|_distinct`, the `_all` facade
//! surface), checked WHOLE-RUN at resolve. These pins fix the corners that the
//! refuted structural-count v1 (false-fired on reconvergent ambiguity) and the
//! v3 first-fork window (post-window gap + over-fire on transient fans) got
//! wrong.

use mettail_languages::{calculator as calc, rholang};
use mettail_prattail::wpda_runtime::{CursorBoundingMode, LatticeTokenSource, WpdaTokenSource};

/// NO-FALSE-FIRE + cross-packing-DUP gate (amdt #1/#6). `int(float(int(3.14)))
/// == 3` explores ~110 structural derivations (peak_R=110) that RECONVERGE to a
/// single reading. A raw-`terms.len()` budget (the refuted v1) would count ~110
/// and false-fire at every small N; the DEDUPED count is 1, so the pure engine
/// returns Ok at EVERY N >= 1 — including N=1, where the top Symbol's many
/// same-semantic-key packings must not be double-counted.
#[test]
fn pure_no_false_fire_on_reconvergent_cast_tower() {
    let input = "int(float(int(3.14))) == 3";
    for n in [1usize, 2, 3, 4, 8, 16] {
        let dag = calc::lex_dag(input).expect("lex cast tower");
        let source = LatticeTokenSource::new(dag);
        let mut pos = 0usize;
        let (terms, weights) = calc::parse_Bool_via_wpda_all_with_source_and_bounding_mode(
            &source,
            &mut pos,
            0,
            CursorBoundingMode::AmbiguityBudget(n),
        )
        .unwrap_or_else(|e| panic!("pure engine must NOT fire at N={n} (1 distinct reading): {e}"));
        assert_eq!(terms.len(), 1, "reconvergent cast tower = one reading at N={n}");
        assert_eq!(terms.len(), weights.len());
        assert_eq!(pos, source.eof_node());
    }
}

/// Parse a rholang Proc `input` under `AmbiguityBudget(n)`; return Ok(display
/// set) or Err(rendered message).
fn proc_budget_at(input: &str, n: usize) -> Result<Vec<String>, String> {
    let dag = rholang::lex_dag(input).expect("lex");
    let source = LatticeTokenSource::new(dag);
    let mut pos = 0usize;
    match rholang::parse_Proc_via_wpda_all_with_source_and_bounding_mode(
        &source,
        &mut pos,
        0,
        CursorBoundingMode::AmbiguityBudget(n),
    ) {
        Ok((terms, _w)) => {
            assert_eq!(pos, source.eof_node(), "`{input}` must consume to EOI at N={n}");
            Ok(terms.iter().map(|t| format!("{t}")).collect())
        },
        Err(e) => Err(format!("{e}")),
    }
}

/// The strict-boundary witness: `@((a)!(0))!()` has two DISTINCT
/// display-inequivalent readings — `@(a!(0))!()` (redundant-quote-elided) and
/// `@((a)!(0))!()` — so `|R|_distinct == 2`.
fn witness_at(n: usize) -> Result<Vec<String>, String> {
    proc_budget_at("@((a)!(0))!()", n)
}

/// STRICT-BOUNDARY genuinely-ambiguous witness (§5 / amdt #7). `|R|_distinct=2`,
/// so the pure engine fires at N=1 (2 > 1) and admits at N=2 (2 <= 2), strict
/// `>`. N=1 fires on BOTH engines (pure actual=2 readings, classic actual=3
/// frontier), both `> 1`.
#[test]
fn genuinely_ambiguous_witness_strict_boundary() {
    // Below the boundary: fire on both engines.
    match witness_at(1) {
        Err(msg) => assert!(
            msg.contains("ambiguity budget 1 exceeded (actual "),
            "N=1 must fire with the engine-neutral wording (got: {msg})"
        ),
        Ok(readings) => panic!("N=1 must fire (|R|_distinct=2 > 1); got Ok({readings:?})"),
    }

    // Pure, at the boundary N=2: admit, and return the FULL exact 2-reading set
    // (P-D exactness — the top-only cap is non-binding when |R|_distinct <= N).
    let readings = witness_at(2).expect("pure: |R|_distinct=2 <= 2 => Ok");
    assert_eq!(readings.len(), 2, "the full 2-reading set survives at the boundary");
    assert!(
        readings.iter().any(|r| r == "@(a!(0))!()"),
        "quote-elided reading present: {readings:?}"
    );
    assert!(
        readings.iter().any(|r| r == "@((a)!(0))!()"),
        "quoted reading present: {readings:?}"
    );

    // Above the boundary: still Ok, same exact set (cap non-binding).
    let readings3 = witness_at(3).expect("pure: 2 <= 3 => Ok");
    assert_eq!(readings3.len(), 2, "N=3 admits the same full 2-reading set");
}

/// v3-MISS pin (§8): an input whose FIRST fork is `<= N` but whose deduped
/// realized count is `> N`. The refuted v3 first-fork window enforced ONLY the
/// first multi-way fork and left later fans UNENFORCED (the "post-window gap");
/// A1 counts ALL readings WHOLE-RUN at resolve, so it catches ambiguity the
/// window structurally missed.
///
/// `@((a)!(0))!() | @((b)!(0))!()` is the parallel composition of two 2-reading
/// sends => `|R|_distinct == 4`, but the leading `@`-dispatch fork is only ~3
/// wide — the readings MULTIPLY at the second send, past the first fork.
/// Measured: the fan-window records `ambiguity_overflows == 0` at N=3 (it does
/// NOT detect an overflow, i.e. the first fork is `<= 3`), so the old v3 window
/// would return Ok(4) at N=3 — yet A1 correctly FIRES (4 > 3). This is the exact
/// gap v3 "reported-but-forgot".
#[test]
fn a1_catches_post_first_fork_ambiguity_v3_would_miss() {
    let input = "@((a)!(0))!() | @((b)!(0))!()";

    // N=3: the first fork (<= 3, measured `ambiguity_overflows==0`) would let the
    // v3 window PASS, but A1 fires on the whole-run count of 4 distinct readings.
    // `actual` is the DISTINCT-READING count (early-fire stops at N+1 = 4).
    let n3_msg = proc_budget_at(input, 3)
        .expect_err("pure: N=3 must fire (4 distinct readings; first fork <= 3)");
    assert!(
        n3_msg.contains("exceeded (actual 4)"),
        "pure fires with the whole-run distinct-reading count (got: {n3_msg})"
    );

    // At the boundary N=4: admit the FULL exact 4-reading set (P-D exactness at a
    // wider fan; the top-only cap is non-binding when |R|_distinct <= N).
    let readings4 = proc_budget_at(input, 4).expect("pure: 4 <= 4 => Ok");
    assert_eq!(readings4.len(), 4, "the full 4-reading set survives at the boundary");
}
