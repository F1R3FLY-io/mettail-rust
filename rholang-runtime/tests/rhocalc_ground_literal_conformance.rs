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
//! equality is a strictly weaker instrument: [`a_firing_comm_does_not_witness_artifact_conformance`]
//! below exhibits two spellings that each COMMIT a COMM in MeTTaIL while carrying DIFFERENT
//! artifacts, only one of which is f1r3node's. Until 2026-07-26 the witness was `-7n` itself —
//! `for(@-7n <- c)` matched `c!(-7n)` only because BOTH sides carried the same *unevaluated*
//! `ENeg`, not because either carried the conforming `GBigInt(-7)`. That row now conforms, so the
//! test carries the still-divergent non-abutted spelling `- 7n` as its live witness instead.
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
//! # Where MeTTaIL diverged — TWO front-end defects, BOTH NOW CLOSED
//!
//! MeTTaIL's lexer preserves the same adjacency distinction (`-7n` → one `BigInt("-7n")` token,
//! `- 7n` → `Minus | BigInt("7n")`), and the parser elects between the two under the declared
//! weight order, whose first tie-breaker below `primary` is `LexicographicWeight::open_len` —
//! MAXIMAL MUNCH (`rigail/src/lex_weight.rs::lex_cmp`). Two things stopped the conforming reading
//! reaching the emitted `Par`.
//!
//! * **(A) two token patterns were missing the sign — ✅ CLOSED 2026-07-26 (`98d861a3`).**
//!   `languages/src/rhocalc.rs` gave `BigInt`, `Fixed` and `Float` a leading `-?` but gave `Int`
//!   and `BigRat` none, so for `-7`, `-7i32`, `-7i64` and `-7r` NO folded reading was generated at
//!   all. Both now carry it (with the `u32` spelling split out so it stays unsigned, mirroring
//!   upstream `unsigned_int_literal`). Measured effect of (A) ALONE: the folded reading appears at
//!   lattice `[0]` for every row, the COLLECTION rows below become conformant outright, `1-7`
//!   still parses as `Sub` (its one-token fork is two adjacent processes ⇒ infeasible ⇒ dies), and
//!   nothing regresses. (A) closed every EMBEDDED and collection-element position and left the
//!   WHOLE-INPUT positions open — those were (B).
//! * **(B) a projection literal was matched inside a longer token — ✅ CLOSED 2026-07-26.**
//!   `emit_projection_isolation_prologue(…, SepSeam::Single)`
//!   (`macros/src/gen/runtime/wpda_codegen/facade.rs`) SHORT-CIRCUITS — `return Ok(__t)` — as soon
//!   as the `@`-projection isolation helper matches. `NegProc . a:Proc |- "-" a : Proc` qualifies
//!   as a sigil-led projection shape under eligibility clause (a) of `derive_projection_iso_shape`
//!   (*"slot 0 is a NON-ident sigil literal — the `@`/`(`/`*`/`-`-led projection shapes"*), so for
//!   a sign-abutted numeral the helper framed the RAW STRING as `- ⟨operand⟩`, sub-parsed the
//!   operand, wrapped in `NegProc` and returned — **destroying the adjacency the lexer preserved**.
//!
//! ★ (B) is NOT the k-best election, and that matters because it is the natural suspect. Measured
//! with `PRATTAIL_CGLL_DIAG` + `PRATTAIL_KBEST_CAND_DIAG` on `-7n`: the single-result walker's
//! accepting root carries a packing family of exactly `{ CastBigInt, CastBigRat }` — there is no
//! `NegProc` candidate in it at all — and `[k-elect]` picks `CastBigInt`, the CONFORMING reading.
//! The election was correct; the facade discarded its answer. The decisive single-variable A/B was
//! the committed kill switch:
//!
//! ```text
//!   Proc::parse_via_wpda("-7n")                          ⇒ NegProc(CastBigInt(NumLit(7)))
//!   PRATTAIL_NO_PROJ_ISOLATION=1 … same call             ⇒ CastBigInt(NumLit(-7))   ← conforming
//! ```
//!
//! The `_all` seam had exactly this defect and it was repaired (#28 / G3, 2026-07-25) by UNIONing
//! with `__all_with_weights_monolithic` instead of short-circuiting; that commit deliberately left
//! the `Single` seam alone, recording *"there is no evidence the election is wrong"*. These rows
//! were that evidence, for the LEXICAL class the note did not consider — and the repair is NOT a
//! second union (which would have flipped `Name::parse("(@Nil)")` and `@Nil!(0)`, exactly as that
//! note warned). It is in the helper's `__Slot::Lit` matcher, which already enforced a
//! token-boundary condition (`before_ok && after_ok`) for WORD-shaped literals — the rule that
//! stops `Nil` matching inside `Nilish` — and enforced none for a punctuation sigil.
//! `macros/src/gen/runtime/wpda_codegen/lit_boundary.rs` now derives, from the grammar's own token
//! patterns, the bytes that can EXTEND each literal into a longer token; for `-` that is
//! `{'.', '0'..'9'}` (RhoCalc's `Int`/`BigInt`/`BigRat`/`Float`/`Fixed` all lead with `-?`, and
//! `Float`/`Fixed` also admit `-.5`), so `-` abutting a digit is a proper prefix of the numeral and
//! the helper declines to the monolithic walker, whose election honours maximal munch. For `@`,
//! `(`, `*`, `[`, `{`, `,`, `<-`, `<=` the derived sets are EMPTY, so their matching is unchanged
//! down to the byte — which is why the two goldens `43ef99aa` named cannot move, and measurably
//! did not.
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

/// ★★ THE (A) RECEIPT, and the row that LOCALIZED defect (B) to the string entry.
///
/// A sign-abutted numeral was CONFORMANT as a collection ELEMENT — `[-7]` emitted f1r3node's
/// `GInt(-7)` — while the very same numeral written alone, or as a send datum, or as a receive
/// pattern, diverged (now [`sign_abutted_numerals_conform_in_every_position`]). That asymmetry was
/// not a mystery, it was the SHAPE of defect (B): the `@`-projection isolation prologue frames only
/// a WHOLE-INPUT σ-led span, so it never pre-empted an element nested inside `[…]` / `{…}`. Those
/// elements were therefore parsed by the monolithic walker, whose election honours maximal munch
/// (`open_len`) and picks the folded reading — exactly what the whole-input rows do now that (B) is
/// closed. Isolating the residue to a whole-input span is what identified the seam.
///
/// ⚠ So this test is load-bearing in BOTH directions. If a future change makes these rows diverge
/// again, (A) has been undone. If it makes them diverge in the SAME way as the whole-input rows,
/// the fix for (B) was applied at the wrong layer (a fold after parsing cannot see adjacency —
/// see [`adjacency_is_honoured`]).
#[test]
fn sign_abutted_numerals_conform_as_collection_elements() {
    for literal in ["[-7]", "[-7i32]", "[-7r]", "[-7n]", "{-7 : 1}", "[-1.5f64]"] {
        assert!(
            agrees(literal),
            "`{literal}` must emit f1r3node's artifact — a sign-abutted numeral is one signed \
             literal TOKEN, and inside a collection nothing pre-empts the walker's election.\n  \
             f1r3node: {}\n  mettail : {}",
            render(&f1r3node_par(literal)),
            render(&mettail_par(literal)),
        );
    }
}

/// ★★★ THE ROW THAT MATTERS TO A PROGRAM — the sign-abutted numeral EMBEDDED in a real term,
/// compared at the ARTIFACT level.
///
/// The three [`positions`] used elsewhere in this file are each a whole-input σ-led span, which is
/// exactly the shape the string-entry projection prologue frames (defect (B), module header). A
/// program is not that shape: it is a `{ … | … }`, a `new`, a `contract` — and the numeral sits
/// somewhere inside it, where the prologue never reached and the walker's election decided. So
/// this row measures the case that actually governs whether MeTTaIL and f1r3node agree on a
/// deployed term, and it is the artifact-level counterpart of
/// `rhocalc_guard_lowering.rs::negative_literal_patterns_match_like_consensus_rholang`. It PASSED
/// while the whole-input rows still failed, which is what proved the residue was a string-entry
/// framing defect rather than a grammar or lowering defect.
///
/// ⚠ It exists BECAUSE that behavioural test is not enough. A COMM firing proves only that the two
/// sides of MeTTaIL's OWN program agree with each other — precisely the blindness
/// [`a_firing_comm_does_not_witness_artifact_conformance`] exhibits. Only this comparison shows the
/// artifact is f1r3node's.
#[test]
fn sign_abutted_numerals_conform_embedded_in_a_program() {
    for literal in ["-7", "-0", "-7i32", "-7i64", "-7n", "-7r", "-1.5f64", "-1.5p2"] {
        let source =
            format!(r#"{{ for(@{literal} <- @"c") {{ @"OUT"!(1) }} | @"c"!({literal}) }}"#);
        assert!(
            agrees(&source),
            "`{source}` must emit f1r3node's artifact. This is the position a real program puts a \
             signed numeral in, and it is the one the projection prologue does not pre-empt.\n  \
             f1r3node: {}\n  mettail : {}",
            render(&f1r3node_par(&source)),
            render(&mettail_par(&source)),
        );
    }
}

/// The non-abutted control for the row above: with the sign detached, BOTH front ends build a real
/// `ENeg` in the pattern, so the artifacts must still agree — and they agree on a DIFFERENT
/// artifact than the abutted spelling produces. A fold applied after parsing would collapse the
/// two spellings together and break this row while appearing to fix the one above.
#[test]
fn non_abutted_signs_conform_embedded_in_a_program() {
    for literal in ["- 7", "-(7)", "- 7n", "- 1.5f64"] {
        let source =
            format!(r#"{{ for(@{literal} <- @"c") {{ @"OUT"!(1) }} | @"c"!({literal}) }}"#);
        assert!(
            agrees(&source),
            "`{source}` has a NON-abutted sign, so both front ends must build an `ENeg` and the \
             artifacts must agree.\n  f1r3node: {}\n  mettail : {}",
            render(&f1r3node_par(&source)),
            render(&mettail_par(&source)),
        );
    }
}

/// Collections carry their elements' artifacts through unchanged, so a conforming element stays
/// conforming inside a list. (The sign-abutted elements have their own row above, because they
/// are the (A) receipt rather than an unremarkable pass-through.)
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
//  2 — THE CLOSED DIVERGENCE, pinned per row and per position. These were the failing rows; each
//      is now its DUAL, so the repair carries a pin at least as strong as the defect had.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Every sign-abutted numeric literal spelling RhoCalc and Rholang share. Each is checked in all
/// three [`positions`], which are exactly the three whole-input numeral-led spans the string-entry
/// projection prologue used to frame as `- ⟨operand⟩`.
///
/// ★ THIS LIST WAS THE DIVERGENCE LIST. Until 2026-07-26 the test below asserted `!agrees` for
/// every row: f1r3node emitted the signed ground literal and MeTTaIL emitted an unevaluated `ENeg`
/// over the unsigned one. It is now its DUAL — the same 8 × 3 grid, asserted to CONFORM — because
/// deleting a pin when its defect is fixed leaves the repair unguarded. The two front-end defects
/// and the order they closed in are in the module header; the mechanical reason this list moved is
/// that `-` abutting a digit is no longer matched as a token by the projection helper's skeleton
/// matcher (`lit_boundary.rs`).
const SIGN_ABUTTED_NUMERALS: [&str; 8] =
    ["-7", "-0", "-7i32", "-7i64", "-7n", "-7r", "-1.5f64", "-1.5p2"];

/// ★★★ THE THREE-COLUMN MATRIX: what f1r3node emits, what MeTTaIL emits, and whether they agree —
/// for every sign-abutted spelling in every position. This is the acceptance criterion of the
/// whole suite, and it prints the matrix on failure so a regression names the exact row.
#[test]
fn sign_abutted_numerals_conform_in_every_position() {
    for literal in SIGN_ABUTTED_NUMERALS {
        for source in positions(literal) {
            assert!(
                agrees(&source),
                "★ `{source}` MUST emit f1r3node's artifact — the sign is part of the numeral \
                 TOKEN on both sides, so no negation node exists to disagree about.\n  \
                 f1r3node: {}\n  mettail : {}",
                render(&f1r3node_par(&source)),
                render(&mettail_par(&source)),
            );
        }
    }
}

/// The one row where the divergence changed the SHAPE of the tree rather than just a leaf — and
/// the row that makes the repair's *precedence* consequence visible.
///
/// `languages/src/rhocalc.rs` states the intent directly — "`NegProc` is declared after `/` and
/// `%` so `-` binds tighter than division (e.g. `-3r/2r` is `(-3r)/2r`)". Until 2026-07-26 it was
/// not so: MeTTaIL elected `ENeg(EDiv(3r, 2r))` = `-(3r/2r)`, because the projection helper framed
/// the whole span as `- ⟨3r/2r⟩` with no precedence awareness at all. f1r3node gets
/// `EDiv(GBigRat(-3), GBigRat(2))` for free, because `-3r` is one token. Both now do.
#[test]
fn sign_binds_tighter_than_division_as_the_grammar_declares() {
    assert!(
        agrees("-3r/2r"),
        "★ `-3r/2r` must be `EDiv(GBigRat(-3), GBigRat(2))` — one signed rational token divided \
         by another, which is also what `rhocalc.rs`'s `NegProc` declaration-order comment \
         claims.\n  f1r3node: {}\n  mettail : {}",
        render(&f1r3node_par("-3r/2r")),
        render(&mettail_par("-3r/2r")),
    );
}

/// ★ THE SAME PRECEDENCE PROPERTY OVER THE ARITHMETIC OPERATORS, added because it MOVED with this
/// repair and an unpinned improvement is indistinguishable from an accident.
///
/// The `- ⟨operand⟩` framing swallowed the whole remaining span, so `-7 + 1` parsed as
/// `ENeg(EPlus(7, 1))` = −8 where f1r3node reads `EPlus(GInt(-7), GInt(1))` = −6. That is a
/// silently WRONG VALUE, not merely a different node, and it was never on the divergence list
/// because the list only covered spans that are numerals end-to-end.
#[test]
fn a_signed_numeral_is_an_operand_not_a_negated_expression() {
    for source in ["-7 + 1", "-7n + 1", "-7 * 2", "-7 - 1", "-1.5f64 + 1.5f64"] {
        assert!(
            agrees(source),
            "★ `{source}`: the sign belongs to the LEFT OPERAND's token, so the operator is the \
             root. A `- ⟨whole span⟩` framing would make the negation the root and change the \
             VALUE.\n  f1r3node: {}\n  mettail : {}",
            render(&f1r3node_par(source)),
            render(&mettail_par(source)),
        );
    }
}

/// ★ WHY BEHAVIOURAL TESTS ARE NOT ENOUGH — kept, with a LIVE witness, after its original witness
/// was repaired.
///
/// The original form of this test used `-7n`: `for(@-7n <- c) | c!(-7n)` committed a COMM in
/// MeTTaIL, so a firing-based matrix scored it green, yet it committed only because BOTH sides
/// carried the identical *unevaluated* `ENeg(GBigInt(7))` — not because either carried f1r3node's
/// `GBigInt(-7)`. That row is now a TRUE pass, so it can no longer witness the hazard, and the
/// test would have been vacuous if it had simply been flipped to `assert_eq!`.
///
/// The hazard itself has not gone anywhere, and the NON-ABUTTED spelling still exhibits it
/// exactly: `- 7n` is a real `ENeg` on both sides, `-7n` is a signed literal on both sides, and the
/// two are DIFFERENT artifacts that a firing observation cannot tell apart — each program's two
/// sides agree with themselves and commit. Only comparing artifacts against f1r3node's normalizer
/// says which one is `-7n`'s.
#[test]
fn a_firing_comm_does_not_witness_artifact_conformance() {
    // Both spellings are self-consistent, which is what makes a COMM fire in each program and what
    // makes a firing-based matrix blind: `for(@X <- c) | c!(X)` commits for X = `-7n` AND for
    // X = `- 7n`, whatever artifact X lowers to.
    let abutted = mettail_par("-7n").expect("MeTTaIL lowers the abutted spelling");
    let spaced = mettail_par("- 7n").expect("MeTTaIL lowers the spaced spelling");
    assert_eq!(
        abutted,
        mettail_par("-7n").expect("re-lowering is deterministic"),
        "the pattern and the datum lower identically — that self-consistency is what makes the \
         COMM fire, and what makes a firing test blind to WHICH artifact fired"
    );

    // ★ THE POINT: self-consistency is satisfied by two DIFFERENT artifacts, so it cannot be the
    // conformance criterion.
    assert_ne!(
        abutted, spaced,
        "★ `-7n` and `- 7n` now lower to the SAME artifact — the adjacency distinction has been \
         lost, which is precisely the failure `adjacency_is_honoured` guards against. A fold \
         applied after parsing is the way this happens."
    );

    // And the oracle says which of the two is f1r3node's reading of `-7n`.
    let spec = f1r3node_par("-7n").expect("f1r3node normalizes `-7n`");
    assert_eq!(abutted, spec, "the abutted spelling must carry f1r3node's signed-literal artifact");
    assert_ne!(
        spaced, spec,
        "the spaced spelling must NOT carry it — it is a genuine `ENeg` in both implementations"
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
