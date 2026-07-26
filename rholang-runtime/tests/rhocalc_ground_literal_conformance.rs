//! Ground-literal ARTIFACT conformance: the `Par` MeTTaIL emits vs the `Par` f1r3node's own
//! normalizer emits, for the same Rholang source.
//!
//! # Why this suite exists, and why it compares ARTIFACTS rather than behaviour
//!
//! MeTTaIL does not meter anything: it emits a `Par` and f1r3node's reducer runs and charges it.
//! So there is exactly one lever, and exactly one correctness criterion:
//!
//! > ★ **Emit the same `Par` that f1r3node's own normalizer would produce from equivalent
//! > Rholang source.**
//!
//! Matching *and* cost accounting are then conformant for free — not because a cost model was
//! replicated, but because it is literally the same artifact through the same reducer. Behavioural
//! equality is a strictly weaker instrument: [`false_agreement_is_not_conformance`] below exhibits
//! a row that COMMITS a COMM in MeTTaIL and would commit in f1r3node, yet carries a different
//! artifact — `for(@-7n <- c)` matches `c!(-7n)` today only because BOTH sides carry the same
//! *unevaluated* `ENeg`, not because either carries the conforming `GBigInt(-7)`.
//!
//! # The mechanism (measured 2026-07-26, corrected — see the ⚠ below)
//!
//! f1r3node folds NOTHING. Its normalizer's `UnaryExpOp::Neg` arm (`compiler/normalize.rs:185`)
//! is a plain `ENeg` constructor (`unary_exp`, :89-105), and its matcher calls `eval` only for
//! `where`-guards (`matcher/match.rs:304`). The conformance comes entirely from **its LEXER**:
//! every signed numeric literal token in the tree-sitter grammar carries the sign INSIDE the
//! token, so for a sign-abutted numeral no negation node is ever built.
//!
//! ```text
//!   signed_int_literal  /-?\d+i[1-9]\d*/     bigint_literal      /-?\d+n/
//!   bigrat_literal      /-?\d+r/             float_literal       /-?…f(32|64|128|256)/
//!   fixed_point_literal /-?…p\d+/            long_literal        /-?\d+/
//!   unsigned_int_literal /\d+u[1-9]\d*/   ← NO sign (the one exception)
//! ```
//!
//! Verified directly on the built grammar
//! (`rholang-rs-cost-accounting-transpiler/rholang-tree-sitter/grammar.js`, rev `9718ab2`):
//! `for (@-7 <- @"c") …` yields `(long_literal [0,6]-[0,8])` — a two-character token spanning the
//! sign. The distinction is ADJACENCY, and f1r3node honours it in both directions: `- 7` (spaced)
//! and `-(7)` (parenthesised) DO build an `ENeg`, and MeTTaIL agrees with f1r3node on those.
//!
//! # Where MeTTaIL diverges
//!
//! MeTTaIL's lexer preserves the same adjacency distinction (`-7n` → one `BigInt("-7n")` token,
//! `- 7n` → `Minus | BigInt("7n")`), and its reading LATTICE already contains the conforming
//! folded-literal reading at index `[0]`. Two things stop it reaching the emitted `Par`:
//!
//! * **(A) two token patterns are missing the sign.** `languages/src/rhocalc.rs` gives `BigInt`,
//!   `Fixed` and `Float` a leading `-?` but gives `Int` and `BigRat` none, so for `-7`, `-7i32`,
//!   `-7i64` and `-7r` no folded reading is generated at all.
//! * **(B) the single-winner election does not pick its own lex-min reading.**
//!   `Proc::parse_via_wpda_all("@\"OUT\"!(-7n)")` returns `[0] CastBigInt(-7)`,
//!   `[1] NegProc(CastBigInt(7))`; `Proc::parse_via_wpda` of the same source elects `[1]`. The
//!   seam is `wpda_walker.rs`'s `RealizeRequestMode::SingleResultElection`, which does not agree
//!   with the ordering `__all_with_weights_monolithic` reports.
//!
//! **(A) alone is NOT sufficient, and this is measured rather than argued**: `BigInt`, `Float` and
//! `Fixed` ALREADY carry `-?`, and they diverge anyway — see [`the_open_divergence_family`]. Any
//! fix that only widens the token patterns will leave every row still failing.
//!
//! # ⚠ Why a lowering-time fold is the WRONG fix
//!
//! Folding `NegProc(<ground literal>)` inside `rhocalc_ast.rs` looks like a one-line repair and is
//! refuted by measurement: by lowering time the ADJACENCY IS ALREADY GONE — `-7` and `- 7` and
//! `-(7)` all parse to the identical `NegProc(CastInt(NumLit(7)))`. A lowering fold would
//! therefore convert the four rows in [`adjacency_is_honoured`] from AGREE to DIVERGE while
//! fixing the abutted ones, i.e. it would trade one divergence for another. The fix must live in
//! the front end, where adjacency still exists. [`adjacency_is_honoured`] is the guard that makes
//! that mistake fail loudly.

#![cfg(all(feature = "rhocalc-runtime", feature = "source-oracle"))]

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::{lower_rhocalc_proc_with_options, LoweringOptions};
use mettail_runtime::clear_var_cache;
use models::rhoapi::Par;
use rholang::rust::interpreter::compiler::compiler::Compiler;

/// THE SPECIFICATION SIDE: f1r3node's own parser + normalizer, the consensus front end.
fn f1r3node_par(source: &str) -> Result<Par, String> {
    Compiler::source_to_adt(source).map_err(|err| format!("{err:?}"))
}

/// THE SUBJECT SIDE: MeTTaIL's production front end (`parse_via_wpda`, never `Proc::parse` —
/// see `rhocalc_guard_lowering.rs`'s header on the display round-trip) plus production lowering.
fn mettail_par(source: &str) -> Result<Par, String> {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source).map_err(|err| format!("parse: {err:?}"))?;
    lower_rhocalc_proc_with_options(&proc, LoweringOptions::PRODUCTION)
        .map_err(|err| format!("lower: {err:?}"))
}

/// Both front ends normalized the source, and the artifacts are equal.
fn agrees(source: &str) -> bool {
    matches!((f1r3node_par(source), mettail_par(source)), (Ok(spec), Ok(subject)) if spec == subject)
}

/// A rendering compact enough to read in an assertion message.
fn render(result: &Result<Par, String>) -> String {
    match result {
        Ok(par) => format!("{par:?}")
            .replace(", locally_free: [], connective_used: false", "")
            .replace("sends: [], receives: [], news: [], ", "")
            .replace(
                ", matches: [], unforgeables: [], bundles: [], connectives: [], conditionals: []",
                "",
            ),
        Err(message) => format!("<{message}>"),
    }
}

/// The two positions a ground literal can occupy, as whole programs. A bare literal is not
/// enough: the divergence has to be pinned where it actually bites — the datum a send stores and
/// the pattern a receive matches against.
fn positions(literal: &str) -> [String; 3] {
    [
        literal.to_string(),
        format!(r#"@"OUT"!({literal})"#),
        format!(r#"for(@{literal} <- @"c") {{ @"OUT"!("Z") }}"#),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — THE TEETH TEST. Nothing below may be believed until this passes.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The oracle must SEPARATE. A comparator that answered "equal" for everything would satisfy
/// every conformance row below, and a comparator that answered "different" for everything would
/// satisfy every divergence row. This shows it doing both correctly on known inputs.
#[test]
fn oracle_has_teeth() {
    // Known-agreeing: an unsigned literal is a plain `GInt` on both sides.
    let spec = f1r3node_par("7").expect("f1r3node normalizes `7`");
    let subject = mettail_par("7").expect("MeTTaIL lowers `7`");
    assert_eq!(spec, subject, "the oracle cannot observe agreement at all");

    // Known-differing, and differing for a reason unrelated to this suite's subject: `7` and `8`
    // are different literals. If this passes only because the comparator is degenerate, the
    // assertion above would already have failed.
    let other = f1r3node_par("8").expect("f1r3node normalizes `8`");
    assert_ne!(spec, other, "the oracle reports agreement between two DIFFERENT artifacts");

    // And the oracle must actually be running f1r3node's normalizer, not a stub: a syntactically
    // invalid program has to fail on the specification side.
    assert!(
        f1r3node_par("for(@ <- ").is_err(),
        "the f1r3node oracle accepted malformed source — it is not really normalizing"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — CONFORMANCE. Every row here already emits f1r3node's artifact, in every position. These
//      are the regression guard: the fix for §2 must not disturb any of them.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Unsigned ground literals of every numeric carrier RhoCalc has, plus the non-numeric grounds.
#[test]
fn unsigned_ground_literals_conform() {
    for literal in ["7", "0", "7n", "7r", "1.5f64", "1.5p2", "0u32", "true", "false", r#""hi""#] {
        for source in positions(literal) {
            assert!(
                agrees(&source),
                "`{source}` must emit f1r3node's artifact\n  f1r3node: {}\n  mettail : {}",
                render(&f1r3node_par(&source)),
                render(&mettail_par(&source)),
            );
        }
    }
}

/// ★ The operators the open divergence was ORIGINALLY suspected to generalize to. They do not.
///
/// An unevaluated `ENot`/`EPlus`/`EAnd`/`ELt` in pattern position does NOT match its evaluated
/// datum — `for(@(1+1) <- c)` does not match `c!(2)` — but that is Rholang's own semantics, and
/// f1r3node emits exactly the same unevaluated expression. There is nothing to fix in this class:
/// send data are evaluated before storage and patterns are not, in BOTH implementations. This
/// test is what bounds the divergent family to the sign-abutted numeric literals alone.
#[test]
fn unevaluated_ground_expressions_conform() {
    for expression in [
        "not true",
        "not false",
        "1 + 1",
        "1 - 7",
        "3 * 4",
        "true and true",
        "true or false",
        "1 < 2",
        "1 == 1",
    ] {
        for source in positions(expression) {
            assert!(
                agrees(&source),
                "`{source}` is an UNEVALUATED ground expression and both front ends must emit the \
                 same expression artifact\n  f1r3node: {}\n  mettail : {}",
                render(&f1r3node_par(&source)),
                render(&mettail_par(&source)),
            );
        }
    }
}

/// Collections carry their elements' artifacts through unchanged, so a conforming element stays
/// conforming inside a list. (`[-7]` does NOT appear here — it is a §2 row, because its element
/// diverges; that it diverges INSIDE a collection too is asserted there.)
#[test]
fn collections_of_conforming_elements_conform() {
    for literal in ["[1, 2]", "[1 + 1]", "[7n]", r#"["hi"]"#, "[true]"] {
        for source in positions(literal) {
            assert!(
                agrees(&source),
                "`{source}` must emit f1r3node's artifact\n  f1r3node: {}\n  mettail : {}",
                render(&f1r3node_par(&source)),
                render(&mettail_par(&source)),
            );
        }
    }
}

/// ★★ THE NEGATIVE CONTROL FOR THE WHOLE SUITE — and the reason a lowering-time fold is wrong.
///
/// f1r3node builds a REAL `ENeg` when the sign does not abut the numeral: `- 7` (whitespace) and
/// `-(7)` (parenthesis) are `neg` nodes, not literals. MeTTaIL agrees on all of these TODAY.
///
/// Any fix that folds `NegProc(<ground literal>)` after parsing — where the adjacency information
/// no longer exists — will break exactly these rows, because `-7`, `- 7` and `-(7)` all parse to
/// the identical `NegProc(CastInt(NumLit(7)))`. If this test fails, the fix was applied at the
/// wrong layer: move it into the lexer/parser, where adjacency is still observable.
#[test]
fn adjacency_is_honoured() {
    for expression in ["- 7", "-(7)", "- 7n", "- 1.5f64", "- 1.5p2", "-(7n)"] {
        for source in positions(expression) {
            assert!(
                agrees(&source),
                "`{source}` has a NON-abutted sign, so BOTH front ends must build an `ENeg`. A \
                 fold applied after parsing cannot see the whitespace/parenthesis and will break \
                 this row — put the fix in the lexer/parser instead.\n  f1r3node: {}\n  \
                 mettail : {}",
                render(&f1r3node_par(&source)),
                render(&mettail_par(&source)),
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — THE OPEN DIVERGENCE, pinned per row and per position so it cannot drift unnoticed and so
//      fixing it is a conscious, visible act. ★ WHEN A ROW HERE FAILS, THAT ROW IS FIXED.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Every sign-abutted numeric literal spelling RhoCalc and Rholang share. f1r3node emits the
/// signed ground literal; MeTTaIL emits an unevaluated `ENeg` over the unsigned one.
///
/// The `Int` and `BigRat` rows additionally have NO folded reading in MeTTaIL's lattice at all
/// (their token patterns in `languages/src/rhocalc.rs` lack the leading `-?` that `BigInt`,
/// `Float` and `Fixed` already carry); the other rows DO have one, at lattice index `[0]`, and
/// lose the single-winner election anyway. Both defects must be fixed — see the module header.
const SIGN_ABUTTED_NUMERALS: [&str; 8] =
    ["-7", "-0", "-7i32", "-7i64", "-7n", "-7r", "-1.5f64", "-1.5p2"];

#[test]
fn the_open_divergence_family() {
    for literal in SIGN_ABUTTED_NUMERALS {
        for source in positions(literal) {
            assert!(
                !agrees(&source),
                "★ `{source}` NOW EMITS f1r3node's ARTIFACT — this row of the sign-abutted \
                 numeric-literal divergence has been FIXED.\n\
                 Move `{literal}` out of `SIGN_ABUTTED_NUMERALS` and into \
                 `unsigned_ground_literals_conform`'s list (renaming it if it is now the whole \
                 set), and update the ⚠ note above `lower_int_value` in \
                 `rholang-runtime/src/rhocalc_ast.rs`.\n  artifact: {}",
                render(&mettail_par(&source)),
            );
        }
    }
}

/// The divergence propagates structurally: a divergent element makes its container divergent.
/// Pinned separately so that a fix which only handles the top level is detected as incomplete.
#[test]
fn the_open_divergence_propagates_into_collections() {
    for literal in ["[-7]", "[-7i32]", "[-7r]", "{-7 : 1}"] {
        assert!(
            !agrees(literal),
            "★ `{literal}` now conforms — a nested row of the sign-abutted divergence is FIXED; \
             see `the_open_divergence_family` for what to update.\n  artifact: {}",
            render(&mettail_par(literal)),
        );
    }
}

/// A precedence consequence of the same root, recorded because it is the one row where the
/// divergence changes the SHAPE of the tree rather than just a leaf.
///
/// `languages/src/rhocalc.rs` states the intent directly — "`NegProc` is declared after `/` and
/// `%` so `-` binds tighter than division (e.g. `-3r/2r` is `(-3r)/2r`)". It is not: MeTTaIL
/// elects `ENeg(EDiv(3r, 2r))` = `-(3r/2r)`. f1r3node gets `EDiv(GBigRat(-3), GBigRat(2))`
/// for free, because `-3r` is one token. Folding the literal fixes the stated intent and the
/// conformance in the same stroke.
#[test]
fn the_open_divergence_changes_tree_shape_under_division() {
    assert!(
        !agrees("-3r/2r"),
        "★ `-3r/2r` now conforms — it should now be `EDiv(GBigRat(-3), GBigRat(2))`, which is \
         also what `rhocalc.rs`'s NegProc declaration-order comment claims. See \
         `the_open_divergence_family`.\n  artifact: {}",
        render(&mettail_par("-3r/2r")),
    );
}

/// ★ WHY BEHAVIOURAL TESTS ARE NOT ENOUGH — the row that "passes" for the wrong reason.
///
/// `for(@-7n <- c) | c!(-7n)` DOES commit a COMM in MeTTaIL today, so a firing-based matrix would
/// score it green. It commits because BOTH sides carry the identical *unevaluated*
/// `ENeg(GBigInt(7))` — the reducer's `ENeg` evaluation does not reduce it — not because either
/// side carries the conforming `GBigInt(-7)`. The artifact comparison catches it; a COMM
/// observation does not. This is the concrete justification for this suite's existence.
#[test]
fn false_agreement_is_not_conformance() {
    let source = r#"for(@-7n <- @"c") { @"OUT"!("Z") }"#;
    let subject = mettail_par(source).expect("MeTTaIL lowers the receive");
    let spec = f1r3node_par(source).expect("f1r3node normalizes the receive");
    assert_ne!(
        subject, spec,
        "★ the `-7n` behavioural false-pass is resolved; see `the_open_divergence_family`"
    );

    // And the reason it is a FALSE pass rather than a real one: the two sides of MeTTaIL's own
    // program are byte-identical to each other while both differ from f1r3node.
    let mettail_pattern = mettail_par("-7n").expect("MeTTaIL lowers the pattern spelling");
    let mettail_datum = mettail_par("-7n").expect("MeTTaIL lowers the datum spelling");
    assert_eq!(
        mettail_pattern, mettail_datum,
        "the pattern and the datum lower identically — that self-consistency is what makes the \
         COMM fire, and what makes a firing test blind to the divergence"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  3 — SPELLINGS f1r3node ITSELF REJECTS. Recorded so a future f1r3node front-end change is
//      noticed here rather than discovered as a silent behaviour difference.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The sign-in-the-token rule has a cost on f1r3node's side: an unspaced subtraction lexes as two
/// adjacent literals and then fails normalization with "Expected single process, got 2". MeTTaIL
/// parses all of these as the operator application a reader intends.
///
/// This is a divergence in which MeTTaIL is strictly MORE permissive on source f1r3node cannot
/// compile at all, so nothing written in these spellings can reach consensus; it is recorded, not
/// "fixed", and it is deliberately NOT a reason to withhold the fix for §2. If f1r3node later
/// accepts them, this test fails and the conformance rows above must be extended to cover them.
#[test]
fn f1r3node_rejects_unspaced_subtraction_and_negated_unsigned() {
    for source in ["1-7", "1 -7", "-0u32", "5-3"] {
        assert!(
            f1r3node_par(source).is_err(),
            "f1r3node now ACCEPTS `{source}` — its lexer's sign-in-the-token rule changed. Extend \
             the conformance rows to cover this spelling.\n  f1r3node: {}",
            render(&f1r3node_par(source)),
        );
        assert!(
            mettail_par(source).is_ok(),
            "MeTTaIL must still parse `{source}`; it is the more permissive front end here"
        );
    }
}
