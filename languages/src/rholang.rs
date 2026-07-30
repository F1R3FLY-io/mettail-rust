#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use num_traits::Zero;
use std::ops::Neg;

/// M-1b — the FORMULA reading of a `Proc` (§18.1), shared by the host guard
/// evaluator (`receive::eval_guard_bool`) and the pattern compiler
/// (`rholang-runtime::rholang_formula`). `pub`, not `pub(crate)`, precisely so
/// there is ONE classification and the two consumers cannot drift apart.
pub mod formula;
/// ★ THE `where` → Dovetail/SFT WIRE, surface half: the `Proc` → [`mettail_prattail::guard_formula::GuardFormula`]
/// encoder, and the COMM-time guard decision derived from it.
///
/// A `where` clause is a SEMANTIC PREDICATE, so it is evaluated by the substrate — at compile
/// time where it is statically decidable (Presburger automata / the propositional algebra /
/// a scalar sort's effective Boolean algebra), at run time otherwise. An `if` condition is
/// unaffected: that is the Rholang interpreter's to decide.
pub mod guard_substrate;
pub(crate) mod pathmap;
/// The HOST receive semantics — including [`receive::eval_guard_bool`], the host `where`-guard
/// evaluator.
///
/// `pub`, not `pub(crate)`, since S-D0: `rholang-runtime::guard_discharge` uses
/// `eval_guard_bool` as the HOST leg of its anti-divergence fence. Compile-time guard discharge
/// acts only when the host evaluator and the MACHINE evaluator (`rho_pure_eval` under the
/// reducer's own `SpatialMatcherOracle`) agree; the host leg is a free redundancy check that
/// turns any divergence between the two into a loud warning rather than an unsound elision.
pub mod receive;
pub(crate) mod runtime;
mod type_inference;
pub(crate) mod zipper;

/// #74 — the value carried by a rholang pathmap entry.
///
/// A pathmap's value slot is OPTIONAL: `{| k |}` binds `k` to nothing, and that
/// is a different term from `{| k : Nil |}`. The generated
/// `Pathmap::PathmapLit(PathMapLit<Proc, PathValue<Proc>>)` payload reflects it;
/// this alias names the value type so downstream crates (the AST lowering, the
/// oracle) can spell it without importing `PathValue` and re-deriving the
/// instantiation. See `runtime/src/path_value.rs`.
pub type PathValueProc = mettail_runtime::PathValue<Proc>;

language! {
    name: Rholang,

    options {
        // Grammar-derived keyword reservation (2026-07-06). Reserving `Nil` (and
        // `error`) removes the over-generated send-on-a-channel-*named*-`Nil`
        // reading (`POutputQuoted(NVar(Free("Nil")), q)`), collapsing the scalar
        // `@Nil!(q)` cohort 2→1. Two fixes make the flip sound:
        //
        //   1. `NULLARY_KEYWORD_LEXFORK_SEED` (`kind_dispatch.rs`): seeds the
        //      reserved nullary keyword's own `Fixed(kw)` reading into the
        //      PrefixDispatch lex-Fork, so `PZero`/`Err` still parse in
        //      prefix/operand position (`*x | Nil`, `@Nil!(Nil)`) once the `Ident`
        //      co-accept is dropped by reservation.
        //   2. `@`-send-sugar canonicalization (`runtime.rs`:
        //      `normalize_send_sugar_canon`, now unconditional):
        //      the number-as-process `@Nil!(n)` projection surface reads as any of
        //      `POutputNil(q)` / `POutputShort(PZero, q)` / `POutput(NQuoteNil, q)`
        //      — all eval-equal to `POutput(NQuote(PZero), q)` but elected
        //      non-deterministically across parse contexts. term_eq now deeply
        //      canonicalizes every `@`-send sugar to its channel-first fold target,
        //      so `query_receive_sugar_with_arithmetic_guard` / `_with_string_guard`
        //      unify regardless of which reading each context elects.
        reserved_keywords: auto,
    },

    types {
        Proc
        Name
        InputBind
        ForRow
        ![i64] as Int
        ![u32] as UInt32
        ![mettail_runtime::CanonicalBigInt] as BigInt
        ![mettail_runtime::CanonicalBigRat] as BigRat
        ![mettail_runtime::CanonicalFixedPoint] as Fixed
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
        // ★★ `Bytes` IS A BYTE ARRAY, NOT A STRING (2026-07-29, ruled).
        //
        // This was `![String] as Bytes`. Both `Str` and `Bytes` were therefore
        // STRING-SHAPED, so the generator emitted a `StringLit` variant for each
        // and a `"…"` literal satisfied BOTH — every string literal in the
        // language had two readings, `CastStr` and `CastBytes`. That was not an
        // election between two designed alternatives; the DECLARATION created the
        // ambiguity, and the disambiguator was left to clean it up.
        //
        // Upstream has no such ambiguity, and cannot express one:
        //
        //   * the wire model (`RhoTypes.proto`) has TWO DISTINCT CARRIERS —
        //     `string g_string = 3` and `bytes g_byte_array = 25`;
        //   * the grammar (`rholang-tree-sitter/grammar.js`) has NO byte-array
        //     literal: the ground-literal choice at `:435-436` is `string_literal`
        //     and `uri_literal` ONLY, and `ByteArray` appears at `:424` solely as a
        //     TYPE NAME in `simple_type` — usable in `matches`/type patterns and
        //     produced by builtins, never written as a literal.
        //
        // So a `"…"` literal is a `GString` upstream, full stop. With a `Vec<u8>`
        // carrier it is a `Str` HERE BY CONSTRUCTION: the ambiguity becomes
        // UNSPELLABLE rather than elected — no disambiguator pin, no dependence on
        // rule declaration order.
        //
        // ⚠⚠ IMPLEMENTED, MEASURED, AND **NOT LANDED** — the carrier line below is
        // commented out and `![String] as Bytes` is restored. Read this before
        // re-attempting it.
        //
        // The change compiles cleanly workspace-wide (`cargo check --workspace
        // --all-targets`, 0 errors, after the sibling `display.rs` emitter fix in
        // `e54e85d7`), and it DOES achieve everything it was meant to:
        //
        //   ★ `Bytes::ListLit(Vec<u8>)` replaces `Bytes::StringLit(String)`, so a
        //     `"…"` literal can no longer be a `Bytes` — the `Str`/`Bytes`
        //     ambiguity becomes UNSPELLABLE rather than elected.
        //   ★ With it, the `semantic_hash` CATEGORY TAG (#151 thread 2) can be
        //     ENABLED and the five goldens it used to move PASS **UNEDITED** —
        //     `matches_forms_are_unambiguous`, `ppar_forms_are_unambiguous`,
        //     `implies_forms_are_unambiguous`,
        //     `the_pre_existing_propositional_forms_keep_their_parse_counts`, and
        //     `rho_rholang_ast::a_s4_ground_width_fold_value_…`. They became TRUE
        //     rather than re-blessed, which was the whole point of holding the tag
        //     back.
        //   ★ All 78 byte-identity / fingerprint / conformance pins PASS: zero
        //     serialized bytes and zero fingerprints moved.
        //
        // ⚠ THE BLOCKER: `Bytes` is left with NO SURFACE FORM AT ALL — not merely
        // "no literal", which is what upstream has, but nothing RENDERABLE either.
        // A `Vec<u8>` payload is not string-shaped, so no `StringLit` is emitted;
        // and because `Bytes` declares no collection delimiters, the Display arm
        // wraps its elements in EMPTY open/close, so `Bytes::ListLit(vec![])`
        // renders as the empty string. MEASURED:
        //
        //   gen_rholang_prop::bytes_display_parse_roundtrip
        //     arb_bytes produced unparseable surface term ""
        //
        // and it takes four sibling round-trips down with it, because `Bytes` is
        // reachable as a `CastBytes` sub-term: `proc_display_parse_roundtrip`,
        // `name_display_parse_roundtrip`, `forrow_display_parse_roundtrip`,
        // `inputbind_display_parse_roundtrip`; plus
        // `unit_rholang_proc_castbytes`, `unit_rholang_auto_bytes_listlit`, and two
        // `testkit::ctor_engine` rows. ELEVEN failures in total.
        //
        // ⚠ These are NOT test-harness artefacts to be gated away. Display→parse is
        // a real invariant of the language, and the change breaks it for an entire
        // category: a `Bytes` value is constructible in Rust and then cannot be
        // rendered. Suppressing the generated rows would hide that rather than fix
        // it.
        //
        // ⇒ Landing this needs `Bytes` to gain a surface form — a GRAMMAR CHANGE
        // the owner has not ruled on, and explicitly outside the scope that was
        // given ("the carrier"). Upstream reaches `ByteArray` through BUILTINS and
        // TYPE PATTERNS rather than literals, so the faithful shape is probably a
        // builtin (`"…".toByteArray()`-style) plus `ByteArray` in the type-pattern
        // position — not a new literal. That is the ruling this waits on.
        //
        // ★ Everything needed to land it in one step is here: uncomment the line
        // below, delete the `![String] as Bytes` line, re-point
        // `rholang_ast.rs::lower_arm_cast_bytes` at `Bytes::ListLit` +
        // `new_gbytearray_par` (see the note there), and re-enable the tag in
        // `macros/src/gen/term_ops/semantic_hash.rs`.
        //
        // ![Vec<u8>] as Bytes
        //
        // ⚠ NOT in scope, and deliberately untouched: `Uri`. Upstream has
        // `string g_uri = 4` with backtick literal syntax which we do not model at
        // all; that is already pinned as unsupported by
        // `languages/tests/rholang_new_official_syntax.rs::uri_declarations_are_not_yet_supported`
        // (asserted `is_err()` so the day it starts parsing is a deliberate
        // change) and tracked as convergence item §17.10-C1. There is also a live
        // interaction to respect when it lands: mettail already spends the
        // backtick on FLT syntax (`FltOpenBacktick`), and the two can coexist only
        // because an FLT requires a lowercase prefix while a URI has none.
        //
        // ⚠ THE STRING CARRIER IS STILL ACTIVE, and this is the defect, not the
        // design: a `"…"` literal has BOTH a `CastStr` and a `CastBytes` reading
        // because both categories are string-shaped. See the block above for the
        // measured replacement and the one ruling it waits on.
        ![String] as Bytes
        ![Vec<Proc>] as List {
            open_parts: ["["],
            close_parts: ["]"],
            sep: ",",
        }
        ![mettail_runtime::HashBag<Proc>] as Bag {
            open_parts: ["#{"],
            close_parts: ["}#"],
            sep: "|",
        }
        ![HashMap<Proc, Proc>] as Map {
            open_parts: ["{"],
            close_parts: ["}"],
            sep: ",",
            key_val_sep: ":",
        }
        ![mettail_runtime::HashSetLit<Proc>] as Set
        ![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap {
            open_parts: ["{|"],
            close_parts: ["|}"],
            sep: ",",
        }
        ![std::sync::Arc<crate::rholang::zipper::ReadZipperLit>] as ReadZipper
        ![std::sync::Arc<crate::rholang::zipper::WriteZipperLit>] as WriteZipper
    },

    // ── Divergence I (2026-07-25): the integer-literal DOMAINS PARTITION ────────────
    //
    // f1r3node's `normalize_ground` (`ground_normalize_matcher.rs:14-50`) is a TOTAL
    // function from a Rholang numeral to exactly ONE ground carrier:
    //
    //     bare digits ▸ GInt        `…i32` / `…i64` ▸ GInt
    //     `…u32` (≤ i64::MAX) ▸ GInt        `…n` ▸ GBigInt
    //
    // so **`Int` is THE ≤64-bit literal carrier** — every Rholang numeral spelling,
    // `…u32` included, is `Int`'s, because the `u32` SUFFIX IS A SPELLING OF A `GInt`
    // rather than a different carrier (`bitnot 0u32` is `-1`, not the 32-bit all-ones
    // `4294967295`; pinned by `rholang_tests::numeral_carrier_is_context_independent::
    // u32_suffix_is_an_i64_literal`). The 32-bit wraparound carrier is reached ONLY
    // through the MeTTaIL-only `uint(x, 32)` cast. Each `eval` below therefore accepts
    // EXACTLY the spellings its own `pattern` declares, and the accepted domains are
    // pairwise DISJOINT, so a numeral's carrier is a function of the numeral TEXT and of
    // nothing else — no election, no context, no parentheses.
    //
    // ⚠ CORRECTED 2026-07-27. This paragraph used to add "and **`UInt32` has NO literal
    // surface**". That clause was FALSE OF THE CODE: `UInt32` declares no `literals { … }`
    // entry, so it inherits the SYNTHESIZED universal acceptor and takes six of `Int`'s
    // spellings — so the "pairwise DISJOINT … no election" claim above holds of the four
    // entries below and NOT of `UInt32`. Nor can the clause simply be made true, because
    // `uint(x, 32)` folds to a `UInt32::NumLit` that `Display` must write and the category
    // must read back. That is open defect D3
    // (`languages/tests/literal_domain_agreement.rs`); the `literals` block below records
    // what was tried and why it was rejected.
    //
    // What this replaced: `BigInt`'s eval used to be `parse_int_lit(text, None)`, a
    // **universal acceptor of every integer spelling**, flatly contradicting its own
    // declared mandatory `…n` tail. Because `home_polymorphic_token_arm` gives every
    // Integer-family category a bare `TokenKind::Integer` arm, `CastBigInt` was a
    // live reading of EVERY numeral and won the lex-min tiebreak by grammar
    // DECLARATION ORDER — while a `(`-grouped numeral reached `CastInt` through a
    // free grouping route. One numeral, two carriers, chosen by parentheses:
    // `"{(1) | 2}"` parsed as `PPar({CastInt(1), CastBigInt(2)})`. Since both this
    // grammar's operators and the consensus reducer's `combine_plus` are
    // carrier-EXACT, that made `int(1,64) + 2` an `error` and `[1,2,3].length() == 3`
    // false. Fixing the ELECTION would have been fixing the wrong layer: the readings
    // it was electing between were ones the grammar should never have admitted.
    //
    // The one deliberate MeTTaIL SUPERSET: an UNSUFFIXED numeral too large for `i64`
    // falls through to `BigInt` (`32478132567813256718` — no Rholang program can
    // express it, so no Rholang-expressible program changes meaning).
    //
    // An explicitly width-suffixed numeral whose value overflows that width
    // (`5000000000u32`) is REJECTED by every category, exactly as Rust rejects it.
    // That is fail-closed and text-determined — it can never yield a divergent
    // *value* — and it is deliberately NOT part of divergence I.
    // ── Divergence I(b) (2026-07-26): the SIGN IS PART OF THE NUMERAL TOKEN ────────
    //
    // f1r3node folds nothing — its `UnaryExpOp::Neg` arm (`compiler/normalize.rs:185`)
    // is a plain `ENeg` constructor and its matcher evaluates only `where`-guards. Its
    // conformance on `-7` is purely LEXICAL: every signed numeric literal in the
    // consensus tree-sitter grammar carries the sign INSIDE the token, so for a
    // SIGN-ABUTTED numeral no negation node is ever built.
    //
    //     long_literal        /-?\d+/            bigint_literal      /-?\d+n/
    //     signed_int_literal  /-?\d+i[1-9]\d*/   bigrat_literal      /-?\d+r/
    //     float_literal       /-?…f(32|64|…)/    fixed_point_literal /-?…p\d+/
    //     unsigned_int_literal /\d+u[1-9]\d*/  ← THE ONE EXCEPTION: no sign
    //
    // The discriminator is ADJACENCY, and f1r3node honours it in BOTH directions:
    // `- 7` (whitespace) and `-(7)` (parenthesis) DO build a real `ENeg`, because the
    // sign cannot be part of the numeral token there. So this is a LEXER fact, not a
    // constant-folding fact, and the fix belongs HERE — where adjacency still exists.
    // By lowering time it is gone: `-7`, `- 7` and `-(7)` all parse to the identical
    // `NegProc(CastInt(NumLit(7)))`, so a fold in `rholang-runtime`'s `lower_int_value`
    // would fix the abutted spellings and BREAK the non-abutted ones (pinned by
    // `rholang_ground_literal_conformance.rs::adjacency_is_honoured`).
    //
    // `BigInt`, `Fixed` and `Float` below already carried `-?`; `Int` and `BigRat` did
    // not, so `-7`/`-7i32`/`-7i64`/`-7r` had NO folded reading in the lattice at all.
    // They now carry it, and the `u32` spelling is SPLIT OUT so that it stays unsigned
    // exactly as `unsigned_int_literal` is upstream — `-0u32` therefore keeps lexing as
    // `Minus`+`Integer` and stays the `NegProc` reading it is today (f1r3node REJECTS
    // that source outright; pinned by
    // `f1r3node_rejects_unspaced_subtraction_and_negated_unsigned`).
    //
    // AMBIGUITY IS PRESERVED, NOT RESOLVED HERE (never-disambiguate-early): the lexer
    // FORKS at a sign-abutted numeral — `-7n` yields BOTH the one-token
    // `BigInt("-7n")` reading and the two-token `Minus`,`BigInt("7n")` reading — and the
    // parser elects between them under the declared weight order, whose first
    // tie-breaker below `primary` is `LexicographicWeight::open_len`, i.e. MAXIMAL MUNCH
    // (`rigail/src/lex_weight.rs::lex_cmp`). That is what keeps `1-7` parsing as
    // subtraction: its one-token reading `1`,`-7` is two adjacent processes, which is
    // infeasible for a single `Proc`, so the fork dies on feasibility and `Minus` wins.
    // (f1r3node cannot compile `1-7` at all — its maximal-munch lexer commits before
    // feasibility is known. MeTTaIL is deliberately the more permissive front end there;
    // pinned in the same test.)
    //
    // The radix forms are signed too (`-0x1F`): `parse_int_lit` strips the sign BEFORE
    // the radix prefix. `parse_rational_lit` does NOT (it splits the radix prefix first),
    // so a negative RADIX rational (`-0x1Fr`) has no folded reading and keeps today's
    // `NegProc` one — text-determined, fail-closed, and unreachable from Rholang, which
    // has no radix literals.
    literals {
        // ⚠ THERE IS DELIBERATELY NO `UInt32` ENTRY HERE, AND THAT IS AN OPEN DEFECT —
        // ledger D3 in `languages/tests/literal_domain_agreement.rs`, which enumerates its
        // six shared spellings exactly so it cannot be forgotten.
        //
        // Without an entry, `UInt32` inherits the SYNTHESIZED default acceptor
        // (`macros/src/gen/runtime/wpda_codegen/prefix.rs::default_eval_body_for_native_kind`
        // ⇒ `parse_int_lit(text, Some(Suffix::U32))`), which takes EVERY unsuffixed integer
        // fitting `u32` — spellings `Int` already owns.
        //
        // ★ THE OBVIOUS REPAIR IS REFUTED — do not re-attempt it. Giving `UInt32` the
        // `…u32` spelling and taking it off `Int` (the shape `languages/src/calculator.rs`
        // uses) was implemented and MEASURED on 2026-07-27, and it changes a VALUE:
        //
        //     bitnot 0u32   ⇒ -1          (today, and what f1r3node computes)
        //     bitnot 0u32   ⇒ 4294967295  (with the spelling moved to `UInt32`)
        //
        // because `normalize_ground` maps `UnsignedIntLiteral{bits ≤ 64, ≤ i64::MAX}` to
        // `GInt` — the `u32` SUFFIX IS A SPELLING OF A `GInt`, not a different carrier
        // (pinned by `rholang_tests::numeral_carrier_is_context_independent::
        // u32_suffix_is_an_i64_literal`). Every Rholang numeral spelling is therefore
        // `Int`'s, which leaves `UInt32` no spelling it may own, and the remaining repair —
        // giving a `UInt32` value the surface of the cast that PRODUCES it, `uint(v, 32)` —
        // is a `Display` codegen change, not a grammar change. See the ledger entry.
        Int {
            // The full `normalize_ground` ≤64-bit suffix set. `(i64)?` alone left
            // `5i32`/`5u32` un-lexable as a single `Int` token even though both are
            // `GInt` upstream.
            //
            // Two alternatives, because the sign covers `long`/`signed_int` but NOT
            // `unsigned_int` (see the divergence I(b) note above): `-?<digits>(i32|i64)?`
            // and the UNSIGNED `<digits>u32`.
            pattern: r"(-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i32|i64)?|(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)u32)";
            eval: ![ {
                // The `…n` tail is BigInt's ALONE; every other spelling that fits i64
                // is Int's. The generated `as_i64()` conversion rejects the rest, which
                // then falls through to `BigInt`'s overflow clause.
                if text.ends_with('n') {
                    Err(())
                } else {
                    mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
                }
            } ]
        }
        BigInt {
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
            eval: ![ {
                // EXACTLY the declared `…n` domain, plus the unsuffixed-overflow
                // superset. Both clauses are decided by the token text alone, and
                // both are disjoint from `Int`'s domain (`¬ends_n ∧ fits_i64`).
                let __lit = mettail_prattail::parse_int_lit(text, None).map_err(|_| ())?;
                let __declared_bigint = text.ends_with('n');
                let __unsuffixed_overflow = matches!(
                    mettail_prattail::IntSuffix::from_text(text),
                    mettail_prattail::IntSuffix::Unsuffixed
                ) && __lit.as_i64().is_none();
                if __declared_bigint || __unsuffixed_overflow {
                    Ok(__lit)
                } else {
                    Err(())
                }
            } ]
        }
        BigRat {
            // `-?` mirrors upstream `bigrat_literal /-?\d+r/` (divergence I(b) above).
            //
            // ── Divergence I(d) (2026-07-27): the COMPOSITE `Nr/Dr` form ────────────────
            //
            // ★ A DELIBERATE WIDENING BEYOND UPSTREAM, and the only change that closes the
            // defect. Upstream's `bigrat_literal` is `/-?\d+r/` — WHOLE rationals only —
            // and that suffices there for a precise reason: **f1r3node folds nothing**, so
            // no upstream normalization ever PRODUCES a rational with a denominator ≠ 1.
            // A front end that never produces one never has to print one.
            //
            // MeTTaIL does produce them. `Div` is a `fold` rule, and its `BigRat` arm is
            // `BigRat::RatLit(*x / *y)`, so `3r / 4r` reduces to `CastBigRat(RatLit 3/4)` —
            // a value of the declared domain `![CanonicalBigRat] as BigRat`, which
            // `arb_bigrat` also draws. `Display` wrote it as `3/4r` (measured): the tail
            // was appended once to `CanonicalBigRat`'s own `3/4` rendering, giving a word
            // that is NOT in the declared literal language, and `BigRat::parse("3/4r")`
            // FAILED (measured: `unexpected "/" after parsing`).
            //
            // DIRECTION CHECK — is `Display` wrong, or the pattern? The pattern. At the
            // BigRat CATEGORY there is no operator that could read a detached `/`: Rholang
            // sites division at `Proc` (`Div . a:Proc, b:Proc`), so unlike the detached
            // SIGN — which `NegBigRat`/`NegProc` genuinely reads — there is no operator
            // form of `3/4` inside `BigRat` for `Display` to fall back on. A1
            // (`parse_BigRat(display(RatLit v)) = RatLit v`) is therefore satisfiable ONLY
            // by a literal spelling, and the pattern is the thing that lacked one.
            //
            // EXPOSURE, MEASURED — unparseability, NOT value corruption. Calculator's twin
            // defect DID corrupt values: `RatLit 3/4` displayed `3/4`, which re-parsed as
            // `IntToBigRat(DivInt 3 4)` — INTEGER division — and evaluated to `0`. Rholang
            // cannot reach that: its broken word `3/4r` keeps the `r` on the right operand,
            // so the right factor stays in the rational carrier and no integer division is
            // expressible. `BigRat::parse("3/4r")` is a hard parse ERROR, which is
            // fail-closed. The defect is that the value has no surface, not that it has a
            // wrong one.
            //
            // WHAT THE DIVERGENCE COSTS, EXACTLY. It claims ONE spelling: the UNSPACED
            // `Nr/Dr`, which upstream lexes as three tokens (`3r`, `/`, `4r`) and
            // normalizes to `EDiv`. In Rholang it now lexes as one `BigRat` token. Three
            // things bound the cost:
            //   * VALUE-PRESERVING. The three-token reading folds to
            //     `CastBigRat(RatLit 3/4)`, which is precisely what the one-token reading
            //     denotes. No Rholang program changes value; only the pre-fold term shape
            //     of the unspaced spelling changes.
            //   * NO SURFACE IS STOLEN. `Div`'s own `Display` writes the SPACED `3r / 4r`
            //     (measured), and any whitespace defeats maximal munch, so every division
            //     term still round-trips to a division term.
            //   * AMBIGUITY PRESERVED, NOT RESOLVED. The lexer forks; the three-token
            //     reading stays in the lattice and is elected wherever the one-token one is
            //     infeasible. Maximal munch (`LexicographicWeight::open_len`) elects the
            //     literal, exactly as it elects the sign-abutted numeral in I(b).
            // The residual is a quoted, UNREDUCED, unspaced `@(3r/4r)`, whose Par carries
            // `GBigRat(3/4)` where f1r3node's carries `EDiv`. That is the same class of
            // cost I(b) accepted in the other direction, and it is the price of being able
            // to print a value the language can compute.
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r(/(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r)?";
            eval: ![ {
                // Already composite-aware and sign-aware — measured before the pattern
                // changed: `parse_rational_lit("3r/4r") = Ok(3/4)` and
                // `parse_rational_lit("-1r/2r") = Ok(-1/2)`. Only the pattern was narrower
                // than its own acceptor.
                mettail_prattail::parse_rational_lit(text).map_err(|_| ())
            } ]
        }
        Fixed {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|\.[0-9](_?[0-9])*)p[0-9](_?[0-9])*";
            eval: ![ { mettail_runtime::parse_fixed_lit(text).map_err(|_| ()) } ]
        }
        Float {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)(f64)?|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?(f64)?)";
            eval: ![ { mettail_runtime::parse_float_lit(text).map_err(|_| ()) } ]
        }
    },

    // L9-5: Rholang goes MODAL for FLT (foreign-language template) guest bodies.
    // Each `FltOpen*` opener pushes a RAW guest mode whose closer POPs back to
    // the host; the mode stack is a purely LEXICAL balancer resolved before the
    // parser runs (the parser sees an already-bracketed FltOpen…FltClose kind
    // sequence). ZERO-REGRESSION rationale: an opener is the longest maximal-munch
    // accept at its start (its delimiter makes it strictly longer than the bare
    // `Ident`/keyword it collides with — `lam\`` @4 beats `lam` @3), so under the
    // Delimiter-Unambiguity Invariant the host mode-0 tokenization of every
    // existing Rholang input is byte-identical (no host source contains
    // `IDENT\``, ` ``` `, or the reserved `box{`). Backtick/fence tags are any
    // lowercase IDENT; the brace tag is the reserved keyword `box` (D-1), so it
    // never collides with PPar's `{ … }`.
    tokens {
        // ── Comments — routed to the retained `COMMENTS` channel (task #18) ──────────────
        //
        // A `-> CHANNEL` token is TRIVIA: the lexer resolves it by the same MAXIMAL MUNCH
        // rule as every other token, and when it wins it is consumed but never delivered to
        // the parse stream — exactly how inter-token whitespace is already consumed. It is
        // RETAINED (with its source `Range`) in `LexResult.streams["COMMENTS"]`, readable by
        // the backend through `lex_with_streams()` + `LexResult::tokens_on_channel` /
        // `hidden_tokens_to_left/right`. It is NOT observable by a running Rholang program:
        // only `DEFAULT` feeds the parser and the program.
        //
        // This REPLACES the `rholang` binary's pre-parse `strip_comments` preprocessor, which
        // deleted the bytes before the lexer ever ran (shifting positions and losing the text
        // irrecoverably). The accepted comment language is deliberately IDENTICAL to what the
        // strip removed, so no program changes meaning:
        //
        //   * `LineComment`  — `//` to the end of the line (or end of input).
        //   * `BlockComment` — `/*` to the FIRST `*/` (flat, C-style, NOT nested), spanning
        //     newlines. Rholang tradition; the strip closed at the first `*/` too.
        //
        // Why the three edge cases the strip hand-coded need no code here:
        //   * `"a // b"`  — `StringLit` is one maximal-munch span from `"` to `"`, so the
        //     `//` inside is consumed as string bytes and is never at a token-start position.
        //   * ``lam`a // b` `` — the FLT guest modes are RAW and declare their own tokens;
        //     `LineComment`/`BlockComment` exist ONLY in the default mode, so a comment marker
        //     inside a guest body is verbatim GUEST TEXT.
        //   * `a / b` vs `a // b` — maximal munch: `//` (2 bytes) beats `Div` (1 byte), so the
        //     comment wins, precisely as the strip decided. Nothing is added to the forest, so
        //     the parse count is unchanged.
        // Both classes are byte-level negations, which `complement_ranges` complements over the
        // FULL 0..=255 byte range — so UTF-8 lead/continuation bytes are members and a comment
        // may contain any text (the demos' box-drawing rules, `λ`, `⟦…⟧`) without truncating.
        LineComment = "//[^\\n]*" -> COMMENTS ;
        BlockComment = "/\\*([^*]|\\*+[^*/])*\\*+/" -> COMMENTS ;

        FltOpenBacktick = "[a-z]+`" push(flt_body_backtick) ;
        FltOpenFence = "[a-z]+```" push(flt_body_fence) ;
        FltOpenBrace = "box\\{" push(flt_body_brace) ;

        raw mode flt_body_backtick {
            FltCloseBacktick = "`" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^`$]+" ;
        }
        raw mode flt_body_fence {
            FltCloseFence = "```" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^`$]+" ;
        }
        raw mode flt_body_brace {
            // #13: a bare `{` inside the brace body self-pushes the guest mode so the
            // mode stack depth-counts nesting; the FLT closes at the DEPTH-0 `}` (the
            // GuestBody body-scan depth-counts tokens whose text is the `{` delimiter).
            FltBraceOpen = "\\{" push(flt_body_brace) ;
            FltCloseBrace = "\\}" pop ;
            Hole = "\\$\\{[^}]*\\}" ;
            GuestChunk = "[^{}$]+" ;
        }
    },

    // ★ THE `where` SLOT IS A SEMANTIC PREDICATE — declared, not inferred.
    //
    // *"If it is in a `where` clause, it is a semantic predicate."* Rholang's `where` guard is
    // typed `cond:Proc` rather than `?cond:Guard`, and that is deliberate: `Guard` switches the
    // parser into the predicate sublanguage, whose runtime `BehavioralPred` is relation queries,
    // quantifiers and AC-matches — with **no** comparison operators, **no** arithmetic, and no
    // nesting inside arguments. `where x == 42` would survive only as a flat relation query, and
    // `where x + y < 10` and `where t matches {P | Q}` would not be expressible at all. Retyping
    // the slot would therefore not make the guard a semantic predicate; it would delete most of
    // the guard language.
    //
    // `guard_slots` says the same thing without the loss. It induces exactly the obligations a
    // `?cond:Guard` slot would — `term:ForRowWhere:guard:cond` and
    // `term:ForRowSingleWhere:guard:cond`, both `BehavioralPredicate` — so no consumer can tell
    // which surface produced them, while the guard stays a full `Proc` expression that
    // `rholang::guard_substrate` encodes into the Dovetail/SFT substrate.
    //
    // It is a DECLARATION: the codegen reads this block, never the `"where"` literal or the
    // parameter's name.
    guards {
        guard_slots {
            ForRowWhere(cond);
            ForRowSingleWhere(cond);
        }
    },

    terms {
        PZero .
        |- "Nil" : Proc;

        PDrop . n:Name  |- "*" n : Proc ;

        // Parallel composition, as a multiset of procs. Equations and rewrites
        // match on `(PPar {…})`.
        //
        // TWO surfaces, both user-facing, both live:
        //   * this braced collection rule, `{ P | Q }`, which builds the
        //     `HashBag` directly, and
        //   * the bare infix `P | Q` (`PParInfix`, declared with the other
        //     infix operators), which folds through `merge_pp_parallel` and
        //     flattens nested `PPar` members into one flat n-ary bag.
        // Both therefore arrive at the same `Proc::PPar(HashBag<Proc>)`.
        //
        // ⚠ THERE WAS A THIRD, `__ppar(p, …)`, DELETED 2026-07-29. It was a
        // vestige: commit `1a3f3490` ("Adds support for braced parallel
        // composition", May 2026) introduced the braced rule above, renamed the
        // pre-existing keyword rule to `PParInternal`, and gave it a fold that
        // degenerated it into the new one — but never removed it. It claimed to
        // be the round-trip display surface for a normalized AST, and that was
        // already false when written: the generated `Display` renders
        // `Proc::PPar` as `{ … | … }`, so no term ever displayed through it.
        // Measured before deletion, `__ppar(Nil, Nil)` did not parse either
        // (`TrailingTokens` at byte 5), so it was unreachable from BOTH
        // directions. Do not reintroduce it; it also cost a reserved keyword.
        //
        // AMBIGUITY, DELIBERATELY PRESERVED: `{ … }` also spells a Map literal
        // (`{ k : v }`), so bare `{}` is genuinely ambiguous between an empty
        // Map and an empty `PPar`. Per rholang semantics that ambiguity needs
        // additional context to resolve, so the parser does NOT resolve it
        // here — `parse_via_wpda_all("{}")` returns BOTH readings (measured: 2,
        // `CastMap(MapLit(HashMapLit({})))` and `PPar(HashBag {})`), and the
        // choice is deferred to a consumer that has the context. Pinned by
        // `par_reading_count_pins::empty_braces_keep_both_the_map_and_the_par_reading`
        // in `languages/tests/rholang_tests.rs`. Non-empty `{ … }` is
        // discriminated by its contents (`:` for a Map entry, `|` for a par
        // element), which is a reading of the input, not a prior decision.
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        POutput . n:Name, q:Proc
        |- n "!" "(" q ")" : Proc ;
        PPersistOutput . n:Name, q:Proc
        |- n "!!" "(" q ")" : Proc ;
        // Empty send sugar: `x!()` parses as `x!([])`.
        POutputEmpty . n:Name
        |- n "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        // Empty persistent send sugar: `x!!()` parses as `x!!([])`.
        PPersistOutputEmpty . n:Name
        |- n "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        // Sugar for polyadic send: `x!(a, b, c)` parses as `x!([a, b, c])`.
        //
        // Placing this rule after unary keeps existing unary send parsing stable.
        POutput2Plus . n:Name, a:Proc, bs:Vec(Proc)
        |- n "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold;
        // Sugar for polyadic persistent send: `x!!(a, b, c)` parses as `x!!([a, b, c])`.
        PPersistOutput2Plus . n:Name, a:Proc, bs:Vec(Proc)
        |- n "!!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::PPersistOutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold;
        // Rholang `@Nil` send sugars.  Placed *before* `POutputQuoted` so the
        // generated dispatcher tries the more specific `@ Nil ! ( q )` shape
        // before the general `@ <Name> ! ( q )` shape, which can't accept the
        // `Nil` keyword in its inner Name slot.
        POutputNil . q:Proc
        |- "@" "Nil" "!" "(" q ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(q.clone()),
            )
        }] fold;
        PPersistOutputNil . q:Proc
        |- "@" "Nil" "!!" "(" q ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(q.clone()),
            )
        }] fold;
        POutputQuoted . n:Name, q:Proc
        |- "@" n "!" "(" q ")" : Proc ![{
            Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rholang::receive::name_pattern_to_proc(&n)))), std::sync::Arc::new(q.clone()))
        }] fold;

        // Generalised `@P!(q)` and `@P!!(q)` send sugars (Rholang style).
        //
        // `POutputQuoted` only accepts shapes where the inner sub-expression
        // parses as a `Name` (e.g. bare identifiers `@c` or NParen-wrapped
        // forms), which excludes literal-typed quoted channels like `@1` or
        // `@"k"`.  `POutputShort` / `PPersistOutputShort` accept any
        // `p:Proc`, mirroring the `NQuoteShort` name shorthand below.
        //
        // Declared *after* `POutputQuoted` so that the NFA dispatcher gives
        // the more specific Name-shape rule first crack at `@<Name>!(q)`,
        // preserving its existing fold semantics; only when that path
        // fails (e.g. inner is a literal) do we fall through to this rule.
        //
        // `prefix(220)` bounds the inner Proc parser's binding power so
        // that `+`, `*`, `|`, etc. between `@` and `!` are NOT consumed
        // into the quoted process — `@a + b!(0)` parses as
        // `(@a) + (b!(0))` (a type error at the Proc level, surfaced
        // explicitly), not `(@(a+b))!(0)`.  Same rationale as
        // `NQuoteShort` below.
        POutputShort . p:Proc, q:Proc
        |- "@" p "!" "(" q ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(q.clone()),
            )
        }] fold prefix(220);
        PPersistOutputShort . p:Proc, q:Proc
        |- "@" p "!!" "(" q ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(q.clone()),
            )
        }] fold prefix(220);

        // ─────────────────────────────────────────────────────────────────
        // CHANNEL_FIRST_EMPTY_SEND (Plan a7425459): `@`-led EMPTY send sugars.
        //
        // These are the empty-payload analogs of the five non-empty `@`-led
        // send rules above (POutputNil / PPersistOutputNil / POutputQuoted /
        // POutputShort / PPersistOutputShort). The non-empty rules SHADOW the
        // full-`@`-Name -> POutputEmpty (rule 6) path at the `@`-cohort
        // dispatch: each `@`-led non-empty rule commits to an unconditional
        // `q:Proc` push after `(`, which dies on the empty `)` and PRUNES the
        // whole-Name lineage that would otherwise reach the Name-`!` mixfix
        // trigger where POutputEmpty fires. Adding these five leaf rules gives
        // every `@`-channel its own EMPTY reading at the SAME `@`-cohort, so
        // `@chan!()` parses to POutput(NQuote(inner), []) — the identical AST
        // POutputEmpty (rule 6) produces for a channel-first send `chan!()`.
        //
        // The empty rules co-exist with the non-empty ones at the `@`-cohort
        // and diverge only at the token AFTER `(`: the empty rule's next
        // guarded literal is `)` (it dies if a Proc is present), the non-empty
        // rule ReplaceAndPushes a `q:Proc` (it dies on `)`). This is the SAME
        // `()`-vs-`(q)` evidence-prune that already resolves plain `chan!()`
        // (POutputEmpty) vs `chan!(q)` (POutput) for Ident channels, lifted one
        // level up to the `@`-prefix. The empty payload is `mk_proc_list([])`
        // = `CastList(ListLit([]))`, byte-identical to POutputEmpty's payload.
        //
        // Ordering mirrors the non-empty twins: the specific `Nil`-keyword
        // shapes first, then the general `n:Name` shape, then the literal-Proc
        // `prefix(220)` shapes last (so the NFA dispatcher tries the more
        // specific inner-shape rules before the catch-all Proc shape).
        POutputNilEmpty .
        |- "@" "Nil" "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        PPersistOutputNilEmpty .
        |- "@" "Nil" "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        POutputQuotedEmpty . n:Name
        |- "@" n "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rholang::receive::name_pattern_to_proc(&n)))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        POutputShortEmpty . p:Proc
        |- "@" p "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold prefix(220);
        PPersistOutputShortEmpty . p:Proc
        |- "@" p "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(vec![])),
            )
        }] fold prefix(220);

        // ─────────────────────────────────────────────────────────────────
        // CHANNEL_FIRST_POLYADIC_SEND (Plan af1f872c): `@`-led POLYADIC (2Plus)
        // send sugars — the exact analog of the five `@`-led EMPTY rules above
        // (POutputNilEmpty / PPersistOutputNilEmpty / POutputQuotedEmpty /
        // POutputShortEmpty / PPersistOutputShortEmpty), ONE ARITY OVER.
        //
        // GAP: `@`-led send rules exist for SCALAR (`@P!(q)`, POutputNil /
        // POutputQuoted / POutputShort :163-214) and for EMPTY (`@P!()`,
        // POutputNilEmpty… :244-278) but NONE for POLYADIC. The channel-first
        // polyadic rules POutput2Plus / PPersistOutput2Plus (:138-158) accept
        // only an Ident channel `n:Name`, so `@Nil!(a,b)` / `@a!(a,b)` /
        // `@Map()!(a,b)` / `@(x|y)!(a,b)` / `@1!(a,b)` all ERR (the `@`-led
        // scalar/empty rules commit to a SINGLE `q:Proc` / `)` after `(` and
        // die on the `a "," bs` polyadic tail, pruning the `@`-Name span that
        // would otherwise reach the Name-`!` mixfix polyadic trigger).
        //
        // THE FIX (grammar-derived, monotone ADDITION of five leaf rules — the
        // SAME emission mechanism the `@`-led scalar and empty rules already
        // use): give every `@`-channel its own POLYADIC reading at the SAME
        // `@`-cohort. The payload is `mk_proc_list([a, ...bs])` = CastList(
        // ListLit([a, ...bs])) — byte-identical to the channel-first
        // POutput2Plus payload; the channel is NQuote(inner), identical to the
        // `@`-led scalar channel construction.
        //
        // ★3-WAY [At,Bang] PARTITION (empty / scalar / 2Plus): the three
        // `@`-led families share the `@ inner ! (` prefix and DIVERGE only at
        // t₁ = token-after-`(` and t₂ = token-after-first-operand:
        //   t₁ = `)`                 ⇒ EMPTY   (`@P!()`,   POutput…Empty)
        //   t₁ = operand, t₂ = `)`   ⇒ SCALAR  (`@P!(q)`,  POutput…Short/Quoted)
        //   t₁ = operand, t₂ = `,`   ⇒ 2PLUS   (`@P!(a,b)`, THESE rules)
        // This is the SAME empty/scalar/2Plus evidence-prune that already
        // resolves plain Ident `a!()` / `a!(q)` / `a!(q,r)` (POutputEmpty /
        // POutput / POutput2Plus), lifted one level up to the `@`-prefix.
        //
        // Ordering mirrors the scalar/empty twins: the specific `Nil`-keyword
        // shapes first, then the general `n:Name` shape (covers `@a`, `@Map()`),
        // then the literal-Proc `prefix(220)` shapes last (covers `@1`, `@(x|y)`
        // — precedence-capped so `+`/`|`/etc. between `@` and `!` are NOT
        // consumed into the quoted process). No `PPersistOutputQuoted2Plus`
        // (there is no `PPersistOutputQuoted` scalar twin either — `@n!!(…)` is
        // served by `PPersistOutputShort2Plus`, `p:Proc`).
        POutputNil2Plus . a:Proc, bs:Vec(Proc)
        |- "@" "Nil" "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold;
        PPersistOutputNil2Plus . a:Proc, bs:Vec(Proc)
        |- "@" "Nil" "!!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold;
        POutputQuoted2Plus . n:Name, a:Proc, bs:Vec(Proc)
        |- "@" n "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rholang::receive::name_pattern_to_proc(&n)))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold;
        POutputShort2Plus . p:Proc, a:Proc, bs:Vec(Proc)
        |- "@" p "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold prefix(220);
        PPersistOutputShort2Plus . p:Proc, a:Proc, bs:Vec(Proc)
        |- "@" p "!!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
            )
        }] fold prefix(220);

        // Internal guard gate used by where-clause gating.
        GuardThen . cond:Proc, body:Proc
        |- "__guard_then" "(" cond "," body ")" : Proc ![{
            crate::rholang::receive::guard_then(&cond, &body)
        }] fold;

        // Internal helper for where-guarded communication.
        // Produces reduced body when match+guard succeed; otherwise returns the original
        // receive/send pair unchanged (blocked communication, identity).
        CommWhere . pat:Proc, n:Name, q:Proc, cond:Proc, body:Proc
        |- "__comm_where" "(" pat "<-" n "," q "," cond "," body ")" : Proc ![{
            crate::rholang::receive::comm_pforwhere_subst(&pat, &n, &q, &cond, &body)
        }] fold;

        // Single pattern/channel binding.
        //
        // Query bind sugar: `ptrn <- x!?(a1, ..., ak)` means "send a request to `x` and
        // bind `ptrn` from a private return channel". This is desugared by `for (...) { ... }`
        // folding in `receive::desugar_for_rows`.
        InputBindQuery . lhs:Name, n:Name, args:Vec(Proc)
        |- lhs "<-" n "!" "?" "(" args.*sep(",") ")" : InputBind ![{
            InputBind::InputBindQuery(
                std::sync::Arc::new(lhs.clone()),
                std::sync::Arc::new(n.clone()),
                args.clone(),
            )
        }] fold;
        InputBindEmptyQuery . n:Name, args:Vec(Proc)
        |- "<-" n "!" "?" "(" args.*sep(",") ")" : InputBind ![{
            InputBind::InputBindEmptyQuery(
                std::sync::Arc::new(n.clone()),
                args.clone(),
            )
        }] fold;
        InputBindQuotedQuery . pat:Proc, n:Name, args:Vec(Proc)
        |- "@" pat "<-" n "!" "?" "(" args.*sep(",") ")" : InputBind ![{
            InputBind::InputBindQuotedQuery(
                std::sync::Arc::new(pat.clone()),
                std::sync::Arc::new(n.clone()),
                args.clone(),
            )
        }] fold;

        InputBindQuoted . pat:Proc, n:Name
        |- "@" pat "<-" n : InputBind ![{
            InputBind::InputBindQuoted(
                std::sync::Arc::new(pat.clone()),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindPolyadic . lhs:Name, lhss:Vec(Name), n:Name
        |- lhs "," lhss.*sep(",") "<-" n : InputBind ![{
            let mut items = Vec::with_capacity(1 + lhss.len());
            items.push(crate::rholang::receive::name_pattern_to_proc(&lhs));
            items.extend(lhss.iter().map(crate::rholang::receive::name_pattern_to_proc));
            InputBind::InputBindQuoted(
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindPersistentPolyadic . lhs:Name, lhss:Vec(Name), n:Name
        |- lhs "," lhss.*sep(",") "<=" n : InputBind ![{
            let mut items = Vec::with_capacity(1 + lhss.len());
            items.push(crate::rholang::receive::name_pattern_to_proc(&lhs));
            items.extend(lhss.iter().map(crate::rholang::receive::name_pattern_to_proc));
            InputBind::InputBindQuotedPersistent(
                std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindQuotedPersistent . pat:Proc, n:Name
        |- "@" pat "<=" n : InputBind ![{
            InputBind::InputBindQuotedPersistent(
                std::sync::Arc::new(pat.clone()),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBind . lhs:Name, n:Name
        |- lhs "<-" n : InputBind ![{
            InputBind::InputBind(
                std::sync::Arc::new(lhs.clone()),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindPersistent . lhs:Name, n:Name
        |- lhs "<=" n : InputBind ![{
            InputBind::InputBindPersistent(
                std::sync::Arc::new(lhs.clone()),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindEmpty . n:Name
        |- "<-" n : InputBind ![{
            InputBind::InputBindEmpty(std::sync::Arc::new(n.clone()))
        }] fold;
        InputBindEmptyPersistent . n:Name
        |- "<=" n : InputBind ![{
            InputBind::InputBindEmptyPersistent(std::sync::Arc::new(n.clone()))
        }] fold;

        // A ForRow is one row of a multi-row for: one or more & binds with an optional where guard.
        //
        // ROOT-P Layer F (design-cycle-2, `ROOT_P_DESIGN_CYCLE2.md`): the six
        // persistent-SPECIFIC ForRow rules that used to sit here —
        //   ForRowPersistentWhere / ForRowPersistentNoWhere /
        //   ForRowSinglePersistentWhere / ForRowSinglePersistentNoWhere /
        //   ForRowSingleEmptyPersistentWhere / ForRowSingleEmptyPersistentNoWhere,
        //   all with a bare `Name "<=" n` head — were DELETED. They were grammar-
        // REDUNDANT: every reading they produced is expressible by the GENERAL
        // ForRow rules below over a persistent InputBind (InputBindPersistent
        // `lhs "<=" n`, InputBindEmptyPersistent `"<=" n`), and the desugar
        // (receive.rs `try_comm_on_pfor_user` / rholang_ast.rs
        // `row_binds_persistent_cond`) is byte-identical. Keeping both made every
        // `<=` element of a `bs.*sep("&")` repetition >=2-way ambiguous on the
        // ENCLOSING RULE (distinct GSS node / weight_rule_idx per reading), the
        // dominant multiplicative GLR fork-explosion (`@Nil<=@Nil&…` 14ms→109s
        // over k=0..4 segments). Deleting them collapses the enclosing-marker
        // multiplier while PRESERVING the realized term-set (the alt-count 3→2 is
        // a redundant-READING removal). FV: ForRowPersistentRuleRedundancy.v
        // (T1 desugar-equal, T2 language-preserved, T3 term-set-preserved,
        // T4 marker-count-drops; zero-admission).
        ForRowWhere . b:InputBind, bs:Vec(InputBind), cond:Proc
        |- b "&" bs.*sep("&") "where" cond : ForRow;

        ForRowNoWhere . b:InputBind, bs:Vec(InputBind)
        |- b "&" bs.*sep("&") : ForRow;

        ForRowSingleWhere . b:InputBind, cond:Proc
        |- b "where" cond : ForRow;

        ForRowSingleNoWhere . b:InputBind
        |- b : ForRow;

        // `for` syntax: semicolon rows nest conceptually (outer = first row); `&` with optional
        // `where` in one row is one receive surface. All parse to a single `PForUser` term; query
        // `!?(...)` and COMM semantics are handled in `receive` + rewrites, not desugared
        // into extra Proc constructors.
        PForUser . rows:Vec(ForRow), body:Proc
        |- "for" "(" rows.*sep(";") ")" "{" body "}" : Proc ![{
            crate::rholang::receive::desugar_for_rows(rows, body)
        }] fold;


        NQuote . p:Proc
        |- "@" "(" p ")" : Name ;

        // Rholang shorthand: `@Nil` parses as `@(Nil)` (= `Name::NQuote(Proc::PZero)`).
        // Implemented as a zero-arg `fold` rule so it lowers to the canonical
        // `NQuote(PZero)` AST node at evaluation time and reuses every existing
        // equation, rewrite, and congruence rule on `NQuote`. Disambiguated from
        // `@(P)` by the trigger pair `"@" "Nil"`: the parser only commits to this
        // rule when it sees the `Nil` keyword immediately after `@`.
        NQuoteNil .
        |- "@" "Nil" : Name ![{
            Name::NQuote(std::sync::Arc::new(Proc::PZero))
        }] fold;

        // Rholang generalised `@P` shorthand: `@P` parses as `Name::NQuote(P)`
        // for any `P:Proc`.  This generalises both `NQuote` (`@(P)`) and
        // `NQuoteNil` (`@Nil`), and `POutputQuoted`'s `@<Name>` shape — the
        // NFA dispatcher tries each `@`-starting rule in declaration order and
        // keeps the first success, so more-specific rules above continue to
        // win where applicable.
        //
        // `prefix(220)` is a cross-category prefix binding-power annotation
        // (honoured by `prattail` for cross-cat rules — see
        // `prattail/src/pipeline.rs`).  It caps the inner Proc parser's
        // `min_bp` at 220, well above any Proc-level infix BP, so `@P` only
        // consumes a high-precedence Proc subterm.  Without it `*@1 + 0`
        // would parse as `*(@(1+0))`; with it, the `+ 0` belongs to the
        // outer expression and `*@1 + 0` parses as `(*@1) + 0`.
        // ★ `canonical` (2026-07-26) — THE DECLARED CANONICAL MEMBER of the `Name`
        // surface-synonymy class `{ NQuote, NQuoteShort, NQuoteNil }`. All three denote
        // `NQuote(p)`; the last two say so in their own fold bodies. `Display` therefore
        // renders EVERY member through this rule's surface, so one denotation has one
        // surface and `Display(Parse(Display(t))) == Display(t)` holds independently of
        // parse context.
        //
        // ★ WHY THIS MEMBER, and not `NQuote`. The choice is not free: it is fixed by a
        // sibling rule's surface. `InputBindQuoted . pat:Proc, n:Name |- "@" pat "<-" n`
        // spells its quoted pattern with the SHORTHAND — `"@" pat`, no parentheses — so an
        // `InputBind` written `@(error) <- @Nil` re-parses to `InputBindQuoted(Err, …)` and
        // renders back as `@error <- @Nil`. Choosing `NQuote` as canonical would therefore
        // leave a surface that still sheds a layer on re-parse; choosing `NQuoteShort`
        // makes the two agree at once. Measured 2026-07-26:
        //
        //     (@(error)) <- @Nil  ─▶ @(error) <- @Nil ─▶ @error <- @Nil ─▶ @error <- @Nil
        //       before: three surfaces, fixpoint at layer 3 (the roundtrip asserts layer 2)
        //     (@(error)) <- @Nil  ─▶ @error <- @Nil   ─▶ @error <- @Nil
        //       after:  one surface, fixpoint at layer 1
        //
        // `prefix(220)` is what makes the shorthand SAFE as the canonical surface: an
        // operand binding looser than 220 is parenthesised by Display's own precedence
        // test, so `NQuote(1 + 2)` still renders `@(1 + 2)` — the same bracket the parser
        // requires, emitted by the same threshold.
        NQuoteShort . p:Proc
        |- "@" p : Name ![{
            Name::NQuote(std::sync::Arc::new(p.clone()))
        }] fold prefix(220) canonical;

        // Parenthesized Name grouping used by `*(x)` compatibility.
        //
        // ★ An INERT GROUPING (`grammar_shapes::classify_inert_grouping_shape`): the body is
        // the identity, so `NParen(n)` and `n` are the same `Name` with two surfaces. There
        // is no second RULE to nominate as canonical — the canonical member IS the wrapped
        // term — so `Display` renders it transparently, forwarding this position's
        // binding-power obligation to the child. The brackets come back from the child's own
        // `own_bp < min_bp` test and from the fence machinery whenever the surface needs
        // them, which is why dropping them cannot make a term unparseable.
        NParen . n:Name
        |- "(" n ")" : Name ![{ n.clone() }] fold;

        // `new` — OFFICIAL RHOLANG SURFACE (tree-sitter `grammar.js:89-93`,
        // BNFC `rholang_mercury.cf:72`):
        //
        //     new:        prec(1, seq('new', $.name_decls, 'in', $._proc))
        //     name_decls: commaSep1($.name_decl)
        //     PNew.       Proc1 ::= "new" [NameDecl] "in" Proc1 ;
        //
        // Rholang IS Rholang, so the declaration list carries NO GROUPING
        // PARENTHESES: `new x, y in { P }`. The pre-2026-07-24 Rholang-only
        // shape `"new" "(" xs ")" "in" "{" p "}"` was a historical divergence
        // and is GONE — there is exactly ONE `new` surface, so no rule pair
        // accepts one string (cf. the ROOT-P Layer-F enclosing-rule-redundancy
        // blowup documented on `ForRow*` above).
        //
        // BINDER-LIST TERMINATOR: the `.*sep(",")` binder loop closes on the
        // FOLLOWING literal, which is now `"in"` instead of `")"` (see
        // `wpda_codegen/binder.rs` `Op(Sep)` ⇒ `close = sp[i+1]`). `in` is a
        // reserved keyword (`reserved_keywords: auto`), so it can never be
        // mistaken for a declared name and the list end is unambiguous.
        //
        // BODY BRACES — the ONE remaining divergence, deliberate and measured.
        // Official Rholang's body is `$._proc` / `Proc1`, i.e. any process, so
        // `new x in stdout!("hi")` is legal there and is a parse error here.
        // Making the body a bare trailing `Proc` was IMPLEMENTED AND MEASURED
        // on 2026-07-24 and REJECTED on evidence:
        //
        //   * A trailing OPEN-ENDED same-category `ParamParse` stops at the
        //     FIRST infix operator, so `new x in 1 + 2` realized
        //     `(new x in 1) + 2` and `new x in a or b` realized
        //     `(new x in a) or b`. Official Rholang puts `+` (Proc8) and `or`
        //     (Proc4) INSIDE the body (Proc1) — a SILENT mis-scope, strictly
        //     worse than rejecting the input.
        //   * It is not fixable with a binding-power annotation: `prefix(3)`
        //     changed only the `|`-inside-a-collection case; `+`/`or` still
        //     escaped the body at every `cur_bp` tried (0 and 3).
        //   * It ADDED ambiguity. Parse counts doubled versus the identical
        //     un-wrapped control: `for(z <- a){*(z)}` 1 → `new x in
        //     for(z <- a){*(z)}` 2; `*(@(0))` 1 → `new x in *(@(0))` 2.
        //   * With the body braced the `|` scope is context-INDEPENDENT and
        //     matches official Rholang: `{ new x in { 0 } | 0 }` is a
        //     two-member par, because the `}` closes the body before the `|`.
        //
        // The delimited body needs no binding-power floor and preserves every
        // pre-change parse count exactly. Reproducing Rholang's `Proc1`-level
        // undelimited body needs real work in the walker's trailing-operand
        // path; tracked as convergence item §17.10-B1. Pins:
        // `languages/tests/rholang_new_official_syntax.rs`.
        PNew . ^[xs].p:[Name* -> Proc]
        |- "new" xs.*sep(",") "in" "{" p "}" : Proc;

        // customize error handling
        // (e.g. filter results by =/= Err)
        Err . |- "error" : Proc;

        // cast rust-native types as processes
        //
        // ★ Divergence I: `CastInt` is declared FIRST among the integer projections.
        //
        // The literal DOMAINS (see the `literals` block) already decide which integer
        // CATEGORY a numeral lands in, so this order can no longer route `1n`/`1u32`
        // anywhere — `Int`'s eval refuses `1n` and `BigInt`'s refuses `1u32` whatever
        // the declaration order is. (The obsolete rationale that used to sit here —
        // "more specific integer kinds before i64 Int so tokens like `1n` / `1u32` are
        // not rejected by the Int prefix arm" — was true only while `BigInt`'s eval was
        // a universal acceptor.)
        //
        // What the order DOES decide is which of the two equally-valid *Proc-level*
        // readings of an `Int`-domain literal is canonical: the direct projection
        // `Int ▸ Proc` (`CastInt`), or the promote-then-project chain
        // `Int ▸ BigInt ▸ Proc` (`IntToBigInt` — auto-injected from
        // `NativeKind::lossless_targets`, which puts `TokenKind::Integer` back into
        // `FIRST(BigInt)` — followed by `CastBigInt`). Both are live at every election
        // site, but they are not equally reachable at all of them: the collection-
        // ELEMENT sites (`[…]`, `{…}`, `Set(…)`, `#{…}#`, `{| |}`) realize only the
        // chain reading, while the top-level and operand sites realize only the direct
        // one. With `CastBigInt` first, that made `1` a `GInt` at top level and a
        // `GBigInt` inside a list *in the same program* — the very context-dependence
        // divergence I is about, merely displaced from the literal layer to the
        // projection layer. Declaring `CastInt` first makes the DIRECT reading
        // canonical at every site, so `{1: 10}.get(1)` and `x!(1) ≡ x!([1])` hold.
        //
        // `CastUInt32` is retained for the `uint(x, 32)` cast's result (the `UInt32`
        // category has no literal surface); its position is immaterial.
        CastBigRat . r:BigRat |- r : Proc;
        CastFixed . x:Fixed |- x : Proc;
        CastFloat . k:Float |- k : Proc;
        CastInt . k:Int |- k : Proc;
        CastBigInt . n:BigInt |- n : Proc;
        CastUInt32 . u:UInt32 |- u : Proc;
        CastBool . k:Bool |- k : Proc;
        CastStr . s:Str |- s : Proc;
        CastBytes . b:Bytes |- b : Proc;
        CastList . l:List |- l : Proc;
        CastBag . b:Bag |- b : Proc;
        CastMap . m:Map |- m : Proc;
        CastSet . s:Set |- s : Proc;
        CastPathmap . m:Pathmap |- m : Proc;
        CastReadZipper . z:ReadZipper |- z : Proc;
        CastWriteZipper . z:WriteZipper |- z : Proc;

        // Numeric casts (see `docs/design/made/native-types/numeric-casting.md`): binary width required.
        IntBinProc . a:Proc, w:Int |- "int" "(" a "," w ")" : Proc ![{
            mettail_runtime::proc_int_bin(a, w)
        }] fold;
        UIntBinProc . a:Proc, w:Int |- "uint" "(" a "," w ")" : Proc ![{
            mettail_runtime::proc_uint_bin(a, w)
        }] fold;
        FloatBinProc . a:Proc, w:Int |- "float" "(" a "," w ")" : Proc ![{
            mettail_runtime::proc_float_bin(a, w)
        }] fold;
        FixedBinProc . a:Proc, w:Int |- "fixed" "(" a "," w ")" : Proc ![{
            mettail_runtime::proc_fixed_bin(a, w)
        }] fold;
        BigintCastProc . a:Proc |- "bigint" "(" a ")" : Proc ![{
            mettail_runtime::proc_bigint_unary(a)
        }] fold;
        BigratCastProc . a:Proc |- "bigrat" "(" a ")" : Proc ![{
            mettail_runtime::proc_bigrat_unary(a)
        }] fold;

        // Unary minus on Int (width args like `int(x, -7)`) and on Proc (`-7`, `-3r/2r`, …).
        // `NegProc` is declared after `/` and `%` so `-` binds tighter than division (e.g. `-3r/2r` is `(-3r)/2r`
        // — pinned by `proj_iso_token_boundary::a_signed_numeral_is_the_operator_s_operand_not_its_argument`).
        // ⚠ Since divergence I(d) that spelling ALSO has a one-token composite-literal reading, `RatLit(-3/2)`;
        // the two denote the same rational, the lattice keeps both, and the demand facade elects the `Div` one.
        NegInt . a:Int |- "-" a : Int ![(-a)] fold;

        // `fold` (not `step`): `step` HOL rules are skipped for non-native categories like Proc.
        FractionProc . a:Proc, b:Proc |- "fraction" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                // ★ Divergence I: the `Int` arm. A bare numeral is a `CastInt` (the
                // `normalize_ground` carrier), so WITHOUT this arm `fraction(1, 2)` — the
                // only spelling of a rational the conformance suite's C3 residue exercises
                // — folds to `error`. The `BigInt` arm below keeps `fraction(1n, 2n)`
                // working; the two carriers are not mixed, matching every other operator.
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(na), Int::NumLit(nb)) => {
                        match mettail_runtime::CanonicalBigRat::try_from_nd(
                            num_bigint::BigInt::from(*na),
                            num_bigint::BigInt::from(*nb),
                        ) {
                            Some(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(na), BigInt::NumLit(nb)) => {
                        match mettail_runtime::CanonicalBigRat::try_from_nd(na.get().clone(), nb.get().clone()) {
                            Some(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Process parallel composition without outer braces (same multiset semantics as `{ P | Q }`).
        // Declared looser than boolean/arithmetic ops so sends/receives compose as expected.
        PParInfix . a:Proc, b:Proc |- a "|" b : Proc ![{
            crate::rholang::runtime::merge_pp_parallel(a.clone(), b.clone())
        }] fold;

        // Infix precedence (declaration order = loosest → tightest for PraTTaIL):
        // implies, or/and, then comparisons, then arithmetic — so `a/b == c/d` and
        // `x==y and z==w` parse correctly.
        //
        // M-0 — material implication, the paper's `φ ⇒ ψ` (notation delta N2: the word
        // `implies`, because `=>` and `⇒` are unavailable in this grammar). Declared
        // IMMEDIATELY BEFORE `Or` because declaration order is loosest → tightest in
        // PraTTaIL and `⇒` is looser than `∨`, so
        //
        //     a or b implies c and d   ⇒   (a or b) implies (c and d)
        //
        // which is the standard reading. ⚠ Associativity: PraTTaIL derives associativity
        // from the binding-power pair it assigns from declaration order, and every
        // same-category infix rule declared this way is LEFT-associative
        // (`prattail/src/binding_power.rs::InfixOperator::associativity`, `left_bp < right_bp`).
        // ★ FIXED: `implies` is declared `right`, so a chain `a implies b implies c` reads
        // `a implies (b implies c)` — classical material implication, and the reading the
        // Heyting `⇒` of `prattail::algebra_tower::HeytingAlgebra::implies` has.
        //
        // It previously omitted the annotation and therefore inherited the infix default,
        // left-associativity, so the chain read `(a implies b) implies c`. That is not a
        // harmless notational choice: the two readings are SEMANTICALLY DIFFERENT, and the
        // left one is not even weaker — it is unrelated. Take `a = false, b = false,
        // c = false`. Right: `false implies (false implies false)` = `true`. Left:
        // `(false implies false) implies false` = `true implies false` = `false`. So a
        // three-term chain could evaluate to the opposite truth value from the one its
        // author wrote, silently, with no diagnostic.
        //
        // The old comment said to "parenthesize a chain that means the latter", which put
        // the burden on every author of every guard forever to work around a one-word
        // omission. `right` is the annotation the macro already supports (`ast/src/grammar.rs`
        // parses it after the eval mode; Calculator's `PowInt`/`PowFloat`/`Tern` use it), so
        // the fix costs one keyword and makes the operator mean what its name means.
        //
        // Semantics: `a implies b ≡ (not a) or b` — material implication on the two-valued
        // Boolean algebra Rholang's `bool` inhabits, which is exactly where the Heyting `⇒`
        // of `prattail::algebra_tower::HeytingAlgebra::implies` lands on a Boolean lattice.
        // The `![…]` fold answers a VALUE only for two ground `bool` operands. Two ground
        // NON-bool operands mean the operator is genuinely undefined at those types ⇒ the
        // `error` term; anything else rebuilds the redex so congruence reduces the operand
        // first and the fold re-fires on the value (`runtime::binary_fallback`). A failed
        // operator must never invent a value (cf. `817ae380`) — hence `Proc::Err`, never a
        // fabricated `BoolLit`. This mirrors `Or`/`And` arm for arm.
        Implies . a:Proc, b:Proc |- a "implies" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!*x || *y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Implies(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold right;

        Or . a:Proc, b:Proc |- a "or" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x || *y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Or(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        And . a:Proc, b:Proc |- a "and" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x && *y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::And(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        // Bitwise (looser precedence than arithmetic)
        // Use `bitor` (not `|`) so `{ P | Q }` and bare `P | Q` stay process parallel composition.
        BitOr . a:Proc, b:Proc |- a "bitor" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x | *y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() | y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x.bitor_aligned(*y)))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::BitOr(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        BitAnd . a:Proc, b:Proc |- a "bitand" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x & *y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() & y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x.bitand_aligned(*y)))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::BitAnd(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        BitNot . a:Proc |- "bitnot" a : Proc ![
            { match &a {
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(!n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r.bitnot()))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(
                        mettail_runtime::CanonicalFixedPoint::new(!fp.unscaled().clone(), fp.places()),
                    ))),
                    _ => Proc::Err,
                },
                // See `runtime::is_ground_operand`: `error` only for a ground operand.
                _ => crate::rholang::runtime::unary_fallback(a, || {
                    Proc::BitNot(std::sync::Arc::new(a.clone()))
                }),
            }}
        ] fold;

        // M-1b — the SPATIAL satisfaction operator: `t matches φ` is true iff the
        // term `t` satisfies the formula `φ`, where `φ` is read as a Rholang
        // PATTERN (§18.1: "a formula is a `Proc` sub-tree that the lowering
        // interprets as a pattern"). It compiles to ONE
        // `ExprInstance::EMatchesBody(EMatches{target, pattern})` — an ordinary
        // boolean `Proc` that composes with the rest of the guard language for
        // free — and is decided by the reducer's OWN spatial matcher through the
        // `SpatialMatch` seam (`rho-pure-eval/src/oracle.rs`, M-1a). MeTTaIL
        // contributes the pattern COMPILER (`rholang-runtime/src/rholang_formula.rs`),
        // never a second matcher.
        //
        // ★ CONVERGENCE, not divergence: official Rholang already has `matches`
        // as a globally reserved keyword and an infix `_proc 'matches' _proc`
        // production at precedence 6 — TIGHTER than `and` (5) and `or` (4), at
        // the level of `==`/`!=` (`rholang-tree-sitter/grammar.js`:33, :275). It
        // is declared here at the loose edge of the comparison block, so
        //
        //     a matches P and b matches Q   ⇒   (a matches P) and (b matches Q)
        //
        // which is the reading the paper's multi-subject guards need, and it is
        // the same relative order official Rholang gives. (Rholang assigns ONE
        // precedence level per declaration, so "the same level as `==`" is not
        // expressible; one step looser is the closest reachable placement, and it
        // differs only on the pathological `a matches b == c`, which reads
        // `a matches (b == c)` here.)
        //
        // ⚠ NON-`fold`, deliberately. Every other operator in this block carries a
        // `![…]` host constant-folding body; `matches` carries none, because there
        // is no host constant fold for a SPATIAL match: deciding it means running
        // AC/separating matching with a remainder, which is the reducer's
        // `list_match_single_` + `sub_pars` + `MaximumBipartiteMatch`, and
        // re-implementing that host-side would be exactly the second, divergent
        // matcher this design exists to avoid. The node therefore stays inert
        // under host normalization; it is decided in guard position by
        // `receive::eval_guard_bool` (which delegates to the generated
        // `Proc::match_pattern` on the fragment it can decide SOUNDLY, and answers
        // "undecided" otherwise) and on the machine by `rho_pure_eval`.
        Matches . a:Proc, p:Proc |- a "matches" p : Proc right;

        // M-1b — the paper's SPATIAL connective `PPar(φ, ψ)` (omnibus :2010),
        // spelled VERBATIM (notation delta N6 is retired for this form). It is
        // the separating conjunction: `t ⊨ PPar(φ,ψ)` iff `t` splits into two
        // parallel parts, one satisfying `φ` and the other `ψ`. The lowering
        // compiles it to the Rholang par-pattern `⟦φ⟧ | ⟦ψ⟧`, whose separating
        // semantics is the reducer's own (`spatial_matcher.rs`'s
        // `list_match_single_` + `sub_pars` + `MaximumBipartiteMatch`) — again, no
        // second matcher.
        //
        // A self-delimiting parenthesized mixfix in the shape of `int(a, w)`, so
        // it takes a PREFIX binding power (`max_infix_bp + PREFIX_BP_OFFSET`) and
        // consumes no infix precedence slot: it cannot perturb the relative order
        // of any existing operator.
        //
        // ⚠ `"PPar"` becomes a RESERVED word. Rholang sets
        // `options { reserved_keywords: auto }` (above), which reserves every
        // identifier-shaped literal terminal, so after this declaration `PPar` can
        // no longer name a variable. That is the whole point — reservation is what
        // makes the leading literal unable to fork against the lowercase call-forms
        // (`int(…)`, `bool(…)`, a user method) — and it is affordable because the
        // name is unused: no `.rho` demo, corpus program, or Rholang test binds
        // `PPar`. The idiomatic host spelling `{ φ | ψ }` (an ordinary `PPar`
        // literal) remains available and compiles to the SAME par-pattern, so a
        // program that wants the connective without the keyword still has it.
        SpatialPPar . a:Proc, b:Proc |- "PPar" "(" a "," b ")" : Proc ;

        Eq . a:Proc, b:Proc |- a "==" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                // Divergence H (closed 2026-07-25): `true == true` used to fall through to the
                // collection fallback and answer `error`, because `Eq` had no `Bool` arm — while
                // Rholang's `==` is STRUCTURAL equality on the whole `Par`
                // (`reduce.rs::combine_eq`, `sv1 == sv2`), which answers `true` for two `GBool`s.
                // Rholang conforms DOWN to Rholang.
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                _ => {
                    // Cross-kind comparison. An operand that is still a REDEX rebuilds the `==`
                    // so congruence reduces it first; `error` is reserved for two ground operands
                    // the collection comparator cannot decide (see `runtime::is_ground_operand`
                    // — without this, `*(@(1)) == 1` answers `error`).
                    if !crate::rholang::runtime::both_ground(a, b) {
                        Proc::Eq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                    } else if let Some(v) = crate::rholang::runtime::compare_collection_equality(&a, &b) {
                        Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(v)))
                    } else {
                        Proc::Err
                    }
                },
            }}
        ] fold same;

        Ne . a:Proc, b:Proc |- a "!=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                // Divergence H (closed 2026-07-25) — the `!=` twin of the `Eq` `Bool` arm above.
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                _ => {
                    // The `!=` twin of the `Eq` cross-kind arm above.
                    if !crate::rholang::runtime::both_ground(a, b) {
                        Proc::Ne(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                    } else if let Some(v) = crate::rholang::runtime::compare_collection_equality(&a, &b) {
                        Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!v)))
                    } else {
                        Proc::Err
                    }
                },
            }}
        ] fold same;

        Gt . a:Proc, b:Proc |- a ">" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Gt(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Lt . a:Proc, b:Proc |- a "<" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Lt(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        GtEq . a:Proc, b:Proc |- a ">=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::GtEq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        LtEq . a:Proc, b:Proc |- a "<=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::LtEq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        // Arithmetic (tighter than == and and/or)
        // ── Arithmetic: a failed operation answers the `error` term, never a value ──────────
        //
        // Every numeric arm below runs its operation through `mettail_runtime::SafeArith`
        // (integers ▸ stdlib `checked_*`; floats ▸ NaN-rejecting IEEE) and maps the `None`
        // — overflow, division by zero, `Inf - Inf` — onto `Proc::Err`, the `error` term
        // declared above (`Err . |- "error" : Proc`).
        //
        // Until 2026-07-25 the `Int` and `Float` arms instead wrote `(**a).clone() + (**b).clone()`,
        // reaching a macro-emitted `impl std::ops::Add for Int` whose failure path FABRICATED
        // `Int::NumLit(Default::default())`: `int(i64::MAX,64) + int(1,64)` folded to `0` and
        // `int(1,64) / int(0,64)` folded to `0` — silent wrong VALUES. That emitter fallback is
        // deleted (`macros/src/gen/native/eval.rs`), so the fabrication is no longer expressible;
        // these arms now match the disposition the `UInt32` / `BigInt` / `BigRat` / `Fixed` arms
        // have always used for ÷0. Pinned by `rholang-runtime/tests/rho_rholang_conformance.rs`
        // (divergences A / A2).
        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_add(*x, *y) {
                            Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                // Raw `x + y` on `u32` PANICS on overflow, and a panic raised inside a fold body
                // aborts the process here (unwinding across Cranelift frames — see the
                // conformance suite's module header), so this arm is checked too.
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        match <u32 as mettail_runtime::SafeArith>::safe_add(*x, *y) {
                            Ok(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() + y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(*x + *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => {
                        // ★ IEEE-754, matching upstream's `combine_plus` `GDouble` arm. RULED 2026-07-29
                        // together with `Div` below: see that arm for the floor argument, the IEEE
                        // citation, and why `nan_is_a_value` is required rather than optional.
                        // The indeterminate forms this admits: `Inf + (-Inf)` and `(-Inf) + Inf` (IEEE 754 §7.2, magnitude subtraction of infinities),
                        // plus `NaN` PROPAGATION from either operand (§6.2). Overflow to `±Inf`
                        // was never declined and is unaffected.
                        match mettail_runtime::nan_is_a_value(
                            <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_add(*x, *y),
                        ) {
                            Ok(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x + *y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(format!("{}{}", x, y)))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Add(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_sub(*x, *y) {
                            Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                // `u32` subtraction underflows (and panics) whenever `x < y`; checked here.
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        match <u32 as mettail_runtime::SafeArith>::safe_sub(*x, *y) {
                            Ok(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() - y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(*x - *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => {
                        // ★ IEEE-754, matching upstream's `combine_minus` `GDouble` arm. RULED 2026-07-29
                        // together with `Div` below: see that arm for the floor argument, the IEEE
                        // citation, and why `nan_is_a_value` is required rather than optional.
                        // The indeterminate forms this admits: `Inf - Inf` and `(-Inf) - (-Inf)` (IEEE 754 §7.2, magnitude subtraction of infinities),
                        // plus `NaN` PROPAGATION from either operand (§6.2). Overflow to `±Inf`
                        // was never declined and is unaffected.
                        match mettail_runtime::nan_is_a_value(
                            <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_sub(*x, *y),
                        ) {
                            Ok(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x - *y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Sub(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_mul(*x, *y) {
                            Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        match <u32 as mettail_runtime::SafeArith>::safe_mul(*x, *y) {
                            Ok(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() * y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(*x * *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => {
                        // ★ IEEE-754, matching upstream's `combine_mult` `GDouble` arm. RULED 2026-07-29
                        // together with `Div` below: see that arm for the floor argument, the IEEE
                        // citation, and why `nan_is_a_value` is required rather than optional.
                        // The indeterminate forms this admits: `0 * ±Inf` and `±Inf * 0`, for either signed zero (IEEE 754 §7.2),
                        // plus `NaN` PROPAGATION from either operand (§6.2). Overflow to `±Inf`
                        // was never declined and is unaffected.
                        match mettail_runtime::nan_is_a_value(
                            <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_mul(*x, *y),
                        ) {
                            Ok(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x * *y))),
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Mul(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Div . a:Proc, b:Proc |- a "/" b : Proc ![
            { match (&a, &b) {
                // `safe_div` is `i64::checked_div`: `None` for BOTH `y == 0` and the single
                // overflowing quotient `i64::MIN / -1`.
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_div(*x, *y) {
                            Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        if *y == 0 { Proc::Err } else { Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x / y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() / y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(*x / *y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    // ★★ IEEE-754 DIVISION, WITH NO ZERO GUARD — deliberately identical to
                    // upstream. This arm HAD a `y == 0.0` guard answering `error`; it was removed.
                    //
                    //   | evaluator | `1.0 / 0.0` | `-1.0 / 0.0` | `0.0 / 0.0` |
                    //   |---|---|---|---|
                    //   | f1r3node's reducer (`reduce.rs` `combine_div`, `GDouble` arm) | `+Inf` | `-Inf` | `NaN` |
                    //   | MeTTaIL's Rholang (this arm)                                  | `+Inf` | `-Inf` | `NaN` |
                    //
                    // ★ RULED 2026-07-29, REVERSING an earlier ruling of the same day that had
                    // kept the refusal (recorded in `ffdc3ad1`). The reversal is not a change of
                    // taste; the earlier ruling misapplied the governing rule, and the rule is:
                    //
                    //   **Upstream is a floor on SEMANTICS, not a ceiling on DIAGNOSTICS.** A
                    //   program upstream ACCEPTS must be accepted here, and must compute the SAME
                    //   VALUE. Diagnostics, error specificity and debuggability may exceed
                    //   upstream freely; the accepted-language and the computed values may not
                    //   diverge from it.
                    //
                    //   The BUG-FIX carve-out permits divergence only where upstream is WRONG.
                    //   ⚠ It does not apply here: IEEE 754 §7.3 DEFINES division of a finite
                    //   non-zero numerator by zero as the correctly-signed infinity (raising the
                    //   `divideByZero` exception, whose default handling is to deliver that
                    //   infinity, not to trap), and `0/0` as the invalid operation delivering a
                    //   `NaN`. Upstream is therefore CORRECT, so the carve-out is unavailable, and
                    //   refusing rejects a program upstream accepts — which the floor forbids.
                    //
                    // The earlier ruling's three arguments, and why each fails:
                    //   * "`±Inf` propagating silently is worse than refusing" — an argument about
                    //     which semantics one would PREFER. The floor is not a preference; a
                    //     consensus implementation that refuses what its peers run does not
                    //     produce a safer network, it produces a fork.
                    //   * "consistent with the five sibling arms" — `Int`, `UInt32`, `BigInt`,
                    //     `BigRat` and `Fixed` have NO representation for an infinity, so `error`
                    //     is the only answer available to them. `Float` does have one. Uniformity
                    //     across carriers that differ in what they can represent is not a
                    //     property worth buying with a divergence.
                    //   * "it is the conservative direction — it can never produce a DIFFERENT
                    //     value for a program both accept" — true, and beside the point: it made
                    //     a program upstream accepts UNACCEPTABLE, which is the other half of the
                    //     floor and the half that was overlooked.
                    //
                    // ⚠⚠ **DELETING THE ZERO GUARD IS NOT ENOUGH, AND WRITING RAW `/` HERE IS
                    // IMPOSSIBLE.** Two traps, both MEASURED, both of which silently produce the
                    // wrong disposition rather than a compile error:
                    //
                    //   1. `<CanonicalFloat64 as SafeArith>::safe_div` routes through
                    //      `finite_or_inf_f64` (`runtime/src/safe_arith.rs:532-542`), which
                    //      preserves `±Inf` but DECLINES `NaN` with
                    //      `UndefinedReason::NotANumber`. So a fix that merely drops the
                    //      `y == 0.0` test still refuses `0.0 / 0.0`, where upstream answers `NaN`.
                    //   2. ⚠ The `/` OPERATOR CANNOT BE USED to get around that. Everything inside
                    //      a `![ … ]` block is rewritten by `macros/src/gen/native/rust_code_rewrite.rs`
                    //      (`binop_to_safe_method`, `:206-215`), which turns every `a / b` into
                    //      `<_ as SafeArith>::safe_div(a, b)?` — including a `/` on raw `f64`s. The
                    //      `?` short-circuits the WHOLE fold body, so the rule does not fire at
                    //      all and the redex survives. Measured: an earlier draft of this arm
                    //      wrote `x.get() / y.get()` and `float(0.0,64) / float(0.0,64)` folded to
                    //      the STUCK TERM `"0.0 / 0.0"` — neither a value nor `error`.
                    //
                    // Hence the explicit `match` below, which suppresses the `?` and converts the
                    // one decline this carrier can produce back into the value IEEE specifies.
                    // `finite_or_inf_f64`'s sole decline is `NotANumber`, and every input that
                    // makes `f64` division yield `NaN` (`0/0`, `Inf/Inf`, a `NaN` operand) is an
                    // input whose IEEE answer IS `NaN` — so the conversion is exact, not a
                    // fallback. A decline for any OTHER reason is still `error`: if `SafeArith`'s
                    // float policy ever grows one, this arm must be revisited rather than guess.
                    //
                    // `SafeArith`'s NaN policy itself is left untouched — the tropical and
                    // log-domain semirings depend on it, and it is not this ruling's subject.
                    //
                    // ⚠ TWO RESIDUAL DIVERGENCES REMAIN, and they are NOT from this arm — they
                    // are `CanonicalFloat64`'s canonicalisation (`runtime/src/canonical_float.rs`
                    // :35-42), which maps every `NaN` to one bit pattern and `-0.0` to `+0.0` so
                    // that `Eq`/`Hash`/`Ord` are well defined for terms:
                    //   * `x / -0.0` answers `+Inf` here and `-Inf` upstream, because `-0.0` is
                    //     not representable as a `Float` term in the first place.
                    //   * a produced `NaN` carries `f64::NAN`'s bits rather than the hardware's.
                    // Both are properties of the CARRIER, not of division, and removing them
                    // would cost the term algebra its `Eq`. They are recorded, not fixed here.
                    (Float::FloatLit(x), Float::FloatLit(y)) => {
                        // Finite quotients and `±Inf` pass `finite_or_inf_f64` untouched;
                        // `nan_is_a_value` re-admits the indeterminate forms `0/0` and `Inf/Inf`,
                        // and `NaN` propagation from either operand, as the VALUE IEEE delivers.
                        // The reason-match lives in that ONE function rather than being copied into
                        // each of the four float arms — see `runtime/src/safe_arith.rs`.
                        match mettail_runtime::nan_is_a_value(
                            <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_div(*x, *y),
                        ) {
                            Ok(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => {
                        match x.checked_div(*y) {
                            Some(q) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(q))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Div(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        Mod . a:Proc, b:Proc |- a "%" b : Proc ![
            { match (&a, &b) {
                // `safe_rem` is `i64::checked_rem`: `None` for `y == 0` and for `i64::MIN % -1`.
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_rem(*x, *y) {
                            Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            Err(_) => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        if *y == 0 { Proc::Err } else { Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x % y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() % y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => {
                        match x.checked_rem(*y) {
                            Some(r) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(r))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                // Not two ground operands: `error` only when the operands ARE data
                // (the operator is undefined at those types); otherwise rebuild the redex so
                // congruence can reduce the operand first. See `runtime::is_ground_operand`.
                _ => crate::rholang::runtime::binary_fallback(a, b, || {
                    Proc::Mod(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold same;

        NegProc . a:Proc |- "-" a : Proc ![
            { match &a {
                // `-i64::MIN` overflows (and panics); `safe_neg` is `checked_neg`.
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(n) => match <i64 as mettail_runtime::SafeArith>::safe_neg(*n) {
                        Ok(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                        Err(_) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(-(*u as i64)))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(-n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r.clone().neg()))),
                    _ => Proc::Err,
                },
                // ★★ THE FOURTH FLOAT ARM, and it was the worst of them. This read
                // `CanonicalFloat64::from(-f.get())`, and `rust_code_rewrite.rs` rewrites unary
                // `-` into `<_ as SafeArith>::safe_neg(..)?` just as it rewrites the binary
                // operators — so `-(0.0/0.0)` short-circuited the fold body and left a STUCK TERM
                // (`-NaN` unreduced), which is neither a value nor `error`. It is spelled
                // explicitly now, through the same adapter as the other three. IEEE 754 §6.3: the
                // sign of a `NaN` is not interpreted, and negation propagates it.
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => match mettail_runtime::nan_is_a_value(
                        <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_neg(*f),
                    ) {
                        Ok(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                        Err(_) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(fp.clone().neg()))),
                    _ => Proc::Err,
                },
                // See `runtime::is_ground_operand`: `error` only for a ground operand.
                _ => crate::rholang::runtime::unary_fallback(a, || {
                    Proc::NegProc(std::sync::Arc::new(a.clone()))
                }),
            }}
        ] fold;

        // Rholang-style collection methods (canonical AST; receiver-first surface).
        //
        // `Map()` is an alias for the empty brace literal `{}`.
        // Method-call forms (`m.get(k)`, `m.size()`, …) are the sole grammar
        // constructors for collection operations. Fold semantics are inlined on
        // each method rule; when operands are not ready the rule returns `Err`
        // and the term stays in method-call form for display.
        MapEmpty .
        |- "Map" "(" ")" : Proc ![{
            Proc::CastMap(std::sync::Arc::new(Map::MapLit(
                mettail_runtime::HashMapLit::<Proc, Proc>::new(),
            )))
        }] fold;

        PathmapEmpty .
        |- "Pathmap" "(" ")" : Proc ![{
            // #74: a pathmap's value slot is optional, so the payload's value
            // type is `PathValue<Proc>` (see `runtime/src/path_value.rs`). An
            // EMPTY pathmap still has zero entries — `Unset` is a value in a slot
            // that exists, never an entry that gets invented.
            Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(
                mettail_runtime::PathMapLit::<Proc, mettail_runtime::PathValue<Proc>>::new(),
            )))
        }] fold;

        MGet . m:Proc, k:Proc
        |- m "." "get" "(" k ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => payload.get(&k).cloned().unwrap_or(Proc::Err),
                    _ => Proc::Err,
                },
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref payload) => {
                        match crate::rholang::pathmap::pathmap_get(payload, &k) {
                            Ok(Some(mettail_runtime::PathValue::Set(v))) => v,
                            // ★★ #74, RULED 2026-07-29 (USER): an UNSET value
                            // ERRS. It does not block, and it does not invent a
                            // value.
                            //
                            // The argument is STRUCTURAL. A stuck term asserts
                            // "this may resolve later"; there is no future state
                            // in which `.get` on a valueless entry becomes
                            // answerable, so blocking would be a promise the term
                            // cannot keep.
                            //
                            // ⚠ DELIBERATE DEPARTURE from the `MSet` precedent
                            // below (user decision 2026-06-30), which stays stuck
                            // on an unencodable path. That shape differs: an
                            // unencodable path is a property of the ARGUMENT and a
                            // later substitution really can make it encodable,
                            // whereas an unset value is a property of the STORED
                            // ENTRY, which `.get` cannot change. RULED, not
                            // inferred — do not "restore consistency" by
                            // reverting it.
                            //
                            // The diagnostic names the DISTINCTION rather than
                            // reading like "key not found", because the key WAS
                            // found — that confusion is the whole reason the
                            // message exists. It reports the pathmap's KIND when
                            // the pathmap is uniformly valueless (the shape the
                            // ruling describes) and flags MIXEDNESS otherwise,
                            // because a mixed pathmap is reachable (see the
                            // commit body's path enumeration) and claiming "this
                            // pathmap has no values" of a mixed one would be
                            // false.
                            //
                            // ⚠ The message rides a debug-build diagnostic, not
                            // the returned value: `Err . |- "error" : Proc` is
                            // NULLARY, so the grammar has no value that can carry
                            // a payload. Reported as a finding rather than worked
                            // around — and `.expect(msg)` is NOT an alternative
                            // here, because the `#153` rewrite turns it into a
                            // `Partiality::Declared` DECLINE, which returns `None`
                            // and leaves the term stuck: the exact disposition
                            // this ruling overturns.
                            Ok(Some(mettail_runtime::PathValue::Unset)) => {
                                #[cfg(debug_assertions)]
                                {
                                    let all_unset = payload.iter().all(|(_, v)| v.is_unset());
                                    if all_unset {
                                        eprintln!(
                                            "[pathmap.get] this pathmap has no values, so \
                                             `.get({})` is not a meaningful operation on it \
                                             — the key IS present; nothing is stored under \
                                             it. An unset value is not `Nil` and not \
                                             absent.",
                                            k,
                                        );
                                    } else {
                                        eprintln!(
                                            "[pathmap.get] this pathmap is MIXED (some \
                                             entries carry values, some do not) and the \
                                             entry for `{}` is one of the valueless ones, \
                                             so `.get({})` has nothing to return — the key \
                                             IS present. An unset value is not `Nil` and \
                                             not absent.",
                                            k, k,
                                        );
                                    }
                                }
                                Proc::Err
                            },
                            Ok(None) | Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        MSet . m:Proc, k:Proc, v:Proc
        |- m "." "set" "(" k "," v ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => {
                        let mut new_map = payload.clone();
                        new_map.insert(k.clone(), v.clone());
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(new_map)))
                    },
                    _ => Proc::Err,
                },
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref payload) => {
                        // #74: `.set(k, v)` means "bind k to v", so the value is
                        // explicitly `Set(v)`. The `Unset` binding is reachable
                        // only from the LITERAL `{| k |}` — no method fabricates
                        // one, and none silently drops one either.
                        match crate::rholang::pathmap::pathmap_put(
                            payload,
                            &k,
                            mettail_runtime::PathValue::Set(v.clone()),
                        ) {
                            Ok(updated) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(updated))),
                            // Invalid path encoding (e.g. empty list path) STAYS STUCK
                            // (user decision 2026-06-30): leave the unreduced `.set(...)`
                            // node rather than silently producing `error`.
                            Err(()) => Proc::MSet(
                                std::sync::Arc::new(m.clone()),
                                std::sync::Arc::new(k.clone()),
                                std::sync::Arc::new(v.clone()),
                            ),
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        MContains . m:Proc, k:Proc
        |- m "." "contains" "(" k ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => {
                        Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(payload.get(&k).is_some())))
                    },
                    _ => Proc::Err,
                },
                Proc::CastSet(inner) => match inner.as_ref() {
                    Set::SetLit(ref payload) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(
                        payload.contains(&crate::rholang::runtime::normalize_collection_element(&k)),
                    ))),
                    _ => Proc::Err,
                },
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref payload) => {
                        match crate::rholang::pathmap::pathmap_has(payload, &k) {
                            Ok(b) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(b))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        MDelete . m:Proc, k:Proc
        |- m "." "delete" "(" k ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => {
                        let mut new_map = payload.clone();
                        new_map.remove(&k);
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(new_map)))
                    },
                    _ => Proc::Err,
                },
                Proc::CastSet(inner) => match inner.as_ref() {
                    Set::SetLit(ref payload) => {
                        let mut new_set = payload.clone();
                        new_set.remove(&crate::rholang::runtime::normalize_collection_element(&k));
                        Proc::CastSet(std::sync::Arc::new(Set::SetLit(new_set)))
                    },
                    _ => Proc::Err,
                },
                Proc::CastList(l) => match (l.as_ref(), &k) {
                    (List::ListLit(v), Proc::CastInt(ii)) => match &**ii {
                        Int::NumLit(n) => {
                            // ★★ #100 — an out-of-range index is an ERROR VALUE, like every
                            // one of this match's five sibling arms. It used to be
                            // `panic!("delete: index out of bounds")`, which ran inside the
                            // D-stage saturation closure on the production `m.delete(k)`
                            // surface: `[1,2].delete(5)` aborted the interpreter instead of
                            // answering. `safeify` demotes `.expect`/`.unwrap` to `?` but it
                            // cannot rewrite a `panic!` — there is no receiver to short-
                            // circuit — so this arm is fixed where it is written.
                            //
                            // A negative index arrives here too: `*n as usize` wraps a
                            // negative `i64` to a huge `usize`, which is `>= vec.len()` for
                            // every representable list, so it takes the same arm rather than
                            // indexing from the end.
                            let idx = *n as usize;
                            if idx >= v.len() {
                                Proc::Err
                            } else {
                                let mut vec = v.clone();
                                vec.remove(idx);
                                crate::rholang::runtime::mk_proc_list(vec)
                            }
                        },
                        _ => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // `.union` is shared between `Map`, `Bag`, `Set`, and `Pathmap`.
        MUnion . a:Proc, b:Proc
        |- a "." "union" "(" b ")" : Proc ![{
            match (&a, &b) {
                (Proc::CastMap(ma), Proc::CastMap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Map::MapLit(pa), Map::MapLit(pb)) => {
                        let mut m = pa.clone();
                        for (k, v) in pb.iter() {
                            m.insert(k.clone(), v.clone());
                        }
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(m)))
                    },
                    _ => Proc::Err,
                },
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => {
                        Proc::CastBag(std::sync::Arc::new(Bag::BagLit(ha.union(hb))))
                    },
                    _ => Proc::Err,
                },
                (Proc::CastSet(sa), Proc::CastSet(sb)) => match (sa.as_ref(), sb.as_ref()) {
                    (Set::SetLit(ha), Set::SetLit(hb)) => {
                        Proc::CastSet(std::sync::Arc::new(Set::SetLit(ha.union(hb))))
                    },
                    _ => Proc::Err,
                },
                (Proc::CastPathmap(ma), Proc::CastPathmap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Pathmap::PathmapLit(pa), Pathmap::PathmapLit(pb)) => {
                        match crate::rholang::pathmap::pathmap_merge(pa, pb) {
                            Ok(merged) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(merged))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        MSize . m:Proc
        |- m "." "size" "(" ")" : Proc ![{
            match &m {
                Proc::CastMap(payload) => match payload.as_ref() {
                    Map::MapLit(ref entries) => {
                        Proc::CastInt(std::sync::Arc::new(Int::NumLit(entries.len() as i64)))
                    },
                    _ => Proc::Err,
                },
                Proc::CastBag(_) => Proc::LLength(std::sync::Arc::new(m.clone())),
                Proc::CastSet(payload) => match payload.as_ref() {
                    Set::SetLit(ref entries) => {
                        Proc::CastInt(std::sync::Arc::new(Int::NumLit(entries.len() as i64)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // `.toByteArray()` is a PURE CONSTRUCTOR — it carries no `![{…}]` fold body, because its
        // semantics belong to the ONE evaluator that owns them: f1r3node's reducer
        // (`rholang/src/rust/interpreter/reduce.rs:4137-4160` — `eval_expr` + `substitute`, then
        // `p.encode_to_vec()`), reached by lowering to `EMethod("toByteArray")`
        // (`rholang-runtime/src/rholang_ast.rs::lower_method`).
        //
        // It previously folded host-side through a hand-maintained FORK of f1r3node's `rhoapi`
        // protobuf schema (`languages/proto/rholang_wire.proto` + `languages/src/rholang/wire.rs`),
        // which was retired because it encoded a DIFFERENT Rholang term than Rholang means:
        // its 7-message schema had no `g_big_int` field, while a plain Rholang integer literal is
        // arbitrary-precision, so `proc_to_par` rejected every collection the grammar produces and
        // `.toByteArray()` folded to `error` on the production parse. It also sorted set/map
        // members by raw protobuf BYTE order where Rholang sorts by `ScoredTerm` VALUE order
        // (`models/src/rust/sorted_par_hash_set.rs:22`) — the two disagree on negative integers.
        MToByteArray . m:Proc
        |- m "." "toByteArray" "(" ")" : Proc;

        MKeys . m:Proc
        |- m "." "keys" "(" ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => crate::rholang::runtime::mk_proc_set(
                        payload.iter().map(|(k, _)| k.clone()),
                    ),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        MValues . m:Proc
        |- m "." "values" "(" ")" : Proc ![{
            match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => crate::rholang::runtime::mk_proc_list(
                        payload.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>(),
                    ),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── Rholang-style List methods ───────────────────────────────────
        LLength . l:Proc
        |- l "." "length" "(" ")" : Proc ![{
            crate::rholang::runtime::fold_proc_length(&l)
        }] fold;

        // `l.nth(i)` — Rholang's `nth` (`reduce.rs::method_table`), which is TOTAL on the
        // carrier: it is defined for every index the language can write, and an out-of-range
        // index is a recoverable failure, never a crash.
        //
        // Divergence **C**, closed 2026-07-25 (was pinned by
        // `rholang-runtime/tests/rho_rholang_conformance.rs`):
        //
        //   1. the index arm accepted only `Proc::CastInt` (a fixed-width `int(i, w)`), so the
        //      DEFAULT Rholang integer literal — which is arbitrary-precision `BigInt` — was
        //      rejected and `[10, 20, 30].nth(1)` answered `error`. Rholang has ONE integer, so
        //      `nth` must accept the one a plain literal produces. Both carriers are accepted
        //      here; a `BigInt` index outside `usize` simply misses the list.
        //   2. an out-of-range index ran `.expect("at: index out of bounds")` INSIDE a fold body.
        //      A panic there cannot be contained in this workspace (unwinding across the
        //      Cranelift-compiled frames of `[profile.dev] codegen-backend = "cranelift"` aborts
        //      the process), so `[1].nth(9)` killed the test binary. It is now the `error` term —
        //      the same fail-closed value every other out-of-domain collection access answers.
        LNth . l:Proc, i:Proc
        |- l "." "nth" "(" i ")" : Proc ![{
            fn nth_index(i: &Proc) -> Option<usize> {
                match i {
                    Proc::CastInt(ii) => match &**ii {
                        Int::NumLit(n) => usize::try_from(*n).ok(),
                        _ => None,
                    },
                    Proc::CastBigInt(ii) => match &**ii {
                        BigInt::NumLit(n) => usize::try_from(n.get()).ok(),
                        _ => None,
                    },
                    Proc::CastUInt32(ii) => match &**ii {
                        UInt32::NumLit(n) => Some(*n as usize),
                        _ => None,
                    },
                    _ => None,
                }
            }
            match &l {
                Proc::CastList(lit) => match lit.as_ref() {
                    List::ListLit(v) => match nth_index(&i) {
                        Some(n) => v.get(n).cloned().unwrap_or(Proc::Err),
                        None => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // `l.last()` — the LAST element of a list.
        //
        // ★ AN ADDITIVE EXTENSION, AND THE GAP IT CLOSES IS REAL. Upstream Rholang's collection
        // remainder is always TRAILING: all four productions in
        // `rholang-rs/rholang-tree-sitter/grammar.js` read `commaSep(…), optional(remainder)` —
        // list (:455), set (:457), map (:459), pathmap (:462) — and ZERO productions place the
        // remainder first. So `[x, ..._]` binds the FIRST element and `[..._, x]` does not parse
        // at all: **the last element of a list is not pattern-reachable in Rholang.** `last()` is
        // the method form of that missing projection. The lookahead FIPS writes it literally —
        // `let @result <- trace.last() in { … }`
        // (`FIPS/approved/2026-01-08-Lookahead/2026-01-08-Lookahead.md:70`, again at `:157`) — so
        // this is FIPS conformance, not an invention.
        //
        // Conservativity, MEASURED and NARROWER than first claimed. The paragraph that stood here
        // asserted that `last` "remains usable as an ordinary name" and cited a fixture
        // (`last_is_still_available_as_an_ordinary_name`) that does not exist under that name —
        // because when it was written it FAILED. Every method terminal is keyword-reserved, and
        // has been since the method-call surface landed: `last`, `nth`, `length`, `keys` and
        // `concat` are all rejected as bare identifiers, while `notamethod` is accepted (the
        // positive control). `last` therefore JOINS an existing reservation set rather than
        // creating one or becoming a special case.
        //
        // The claim that survives is the true, narrower one: no upstream program that does not
        // use a METHOD NAME as a bare identifier is affected. Pinned by
        // `languages/tests/rholang_tests.rs::native_ops::list::
        // last_joins_the_reserved_method_names_and_is_not_a_special_case`, which carries the
        // measurement table. The residual reservation defect is LOGGED, not fixed here.
        //
        // ⚠ TOTALITY IS INHERITED FROM `LNth`, NOT CHOSEN HERE. `LNth` (directly above) is TOTAL:
        // a non-list receiver, a non-integer index and an index past the end all answer the
        // `error` term (`Err . |- "error" : Proc`), the last of them through
        // `.cloned().unwrap_or(Proc::Err)`. "There is no element there" is exactly that case, and
        // the empty list is exactly that shape — so `[].last()` is `error`, the SAME value
        // `[].nth(0)` answers, reached through the SAME combinator. No new error variant is
        // introduced. And, as recorded for `LNth`, a fold body must never panic: unwinding across
        // the Cranelift-compiled frames of `[profile.dev] codegen-backend = "cranelift"` aborts
        // the process, so `.expect(…)`/indexing here would kill the test binary rather than fail.
        //
        // ★ MACHINE PATH: ROUTED as of 2026-07-28. `last` IS a key of the interpreter's
        // `method_table` (`rholang/src/rust/interpreter/reduce.rs:9023-9089` in the pinned
        // `../f1r3node-rust-mettail`: `nth` at :9025, `last` at :9026, `length` at :9088), so
        // `l.last()` lowers to `EMethod("last")` and the REDUCER answers. This paragraph
        // previously recorded the opposite — that there was nothing to route to and `LLast` was
        // therefore C3 residue, fail-closed and named. That was true until the key existed.
        //
        // ⚠ The interpreter method is NATIVE, not the desugaring `l.last()` ⇒
        // `l.nth(l.length() - 1)`. The desugaring is expressible entirely in methods that already
        // existed and would have run with no interpreter change at all, but it names the receiver
        // TWICE, so the receiver is EVALUATED twice — and duplicated evaluation is duplicated gas.
        // `last_method` evaluates the receiver ONCE and projects at `len - 1` through the same
        // bounds-checked `local_nth` helper `nth_method` uses, which is also why `[].last()` and
        // `[].nth(0)` cannot answer differently on the machine: they are the same call.
        //
        // ⚠ LANE DISCIPLINE. Routing does NOT make the fold body dead, and it does not make the
        // two lanes identical out of domain: the FOLD answers the `error` term below, while the
        // MACHINE raises a recoverable `index out of bound` reduction error — exactly the split
        // `LNth` already has, where the reducer's answer is the normative one. Agreement is a
        // within-lane property. Pinned on the machine by
        // `rho_rholang_conformance.rs::last_executes_on_the_machine_and_is_not_the_first_element`
        // and `::last_on_the_empty_list_agrees_with_nth_zero_on_the_machine`; the bag ABI gate
        // that routing required is pinned by `::c1_bag_length_and_nth_are_gated_at_lowering`.
        LLast . l:Proc
        |- l "." "last" "(" ")" : Proc ![{
            match &l {
                Proc::CastList(lit) => match lit.as_ref() {
                    List::ListLit(v) => v.last().cloned().unwrap_or(Proc::Err),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        LConcat . l:Proc, r:Proc
        |- l "." "concat" "(" r ")" : Proc ![{
            match (&l, &r) {
                (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
                    (List::ListLit(va), List::ListLit(vb)) => {
                        let mut o = va.clone();
                        o.extend(vb.iter().cloned());
                        crate::rholang::runtime::mk_proc_list(o)
                    },
                    _ => Proc::Err,
                },
                (Proc::CastStr(sa), Proc::CastStr(sb)) => match (sa.as_ref(), sb.as_ref()) {
                    (Str::StringLit(x), Str::StringLit(y)) => {
                        Proc::CastStr(std::sync::Arc::new(Str::StringLit(format!("{}{}", x, y))))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── rholang Bag methods ──────────────────────────────────────────
        BCount . b:Proc, e:Proc
        |- b "." "count" "(" e ")" : Proc ![{
            match &b {
                Proc::CastBag(bag) => match bag.as_ref() {
                    Bag::BagLit(h) => {
                        let normalized = crate::rholang::runtime::normalize_bag_elements(h);
                        let elem = match &e {
                            Proc::PDrop(n) => match n.as_ref() {
                                Name::NQuote(p) => p.as_ref().clone(),
                                Name::NParen(inner) => match inner.as_ref() {
                                    Name::NQuote(p) => p.as_ref().clone(),
                                    _ => e.clone(),
                                },
                                _ => e.clone(),
                            },
                            _ => e.clone(),
                        };
                        Proc::CastInt(std::sync::Arc::new(Int::NumLit(
                            mettail_runtime::HashBag::count(&normalized, &elem) as i64,
                        )))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        BDiff . a:Proc, b:Proc
        |- a "." "diff" "(" b ")" : Proc ![{
            match (&a, &b) {
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => {
                        Proc::CastBag(std::sync::Arc::new(Bag::BagLit(ha.diff(hb))))
                    },
                    _ => Proc::Err,
                },
                (Proc::CastSet(sa), Proc::CastSet(sb)) => match (sa.as_ref(), sb.as_ref()) {
                    (Set::SetLit(ha), Set::SetLit(hb)) => {
                        Proc::CastSet(std::sync::Arc::new(Set::SetLit(ha.difference(hb))))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        BRemove . a:Proc, e:Proc
        |- a "." "remove" "(" e ")" : Proc ![{
            match &a {
                Proc::CastBag(b) => match b.as_ref() {
                    Bag::BagLit(h) => {
                        let normalized = crate::rholang::runtime::normalize_bag_elements(h);
                        let elem = match &e {
                            Proc::PDrop(n) => match n.as_ref() {
                                Name::NQuote(p) => p.as_ref().clone(),
                                Name::NParen(inner) => match inner.as_ref() {
                                    Name::NQuote(p) => p.as_ref().clone(),
                                    _ => e.clone(),
                                },
                                _ => e.clone(),
                            },
                            _ => e.clone(),
                        };
                        Proc::CastBag(std::sync::Arc::new(Bag::BagLit(normalized.remove_one(&elem))))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── Pathmap methods ──────────────────────────────────────────────
        PRestrict . a:Proc, b:Proc
        |- a "." "restrict" "(" b ")" : Proc ![{
            match (&a, &b) {
                (Proc::CastPathmap(ma), Proc::CastPathmap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Pathmap::PathmapLit(pa), Pathmap::PathmapLit(pb)) => {
                        match crate::rholang::pathmap::pathmap_restrict(pa, pb) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PSubtract . a:Proc, b:Proc
        |- a "." "subtract" "(" b ")" : Proc ![{
            match (&a, &b) {
                (Proc::CastPathmap(ma), Proc::CastPathmap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Pathmap::PathmapLit(pa), Pathmap::PathmapLit(pb)) => {
                        match crate::rholang::pathmap::pathmap_subtract(pa, pb) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PMeet . a:Proc, b:Proc
        |- a "." "meet" "(" b ")" : Proc ![{
            match (&a, &b) {
                (Proc::CastPathmap(ma), Proc::CastPathmap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Pathmap::PathmapLit(pa), Pathmap::PathmapLit(pb)) => {
                        match crate::rholang::pathmap::pathmap_meet(pa, pb) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PGetSubtrie . m:Proc
        |- m "." "getSubtrie" "(" ")" : Proc ![{
            match &m {
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::path_get_subtrie(lit) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_get_subtrie(z.as_ref()) {
                        Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PGetSubtrieAt . m:Proc, p:Proc
        |- m "." "getSubtrieAt" "(" p ")" : Proc ![{
            match (&m, &p) {
                (Proc::CastPathmap(inner), path) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::path_get_subtrie_at(lit, path) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PReadZipper . m:Proc
        |- m "." "readZipper" "(" ")" : Proc ![{
            match &m {
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::read_zipper_root(lit) {
                            Ok(z) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(z)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PReadZipperAt . m:Proc, p:Proc
        |- m "." "readZipperAt" "(" p ")" : Proc ![{
            match (&m, &p) {
                (Proc::CastPathmap(inner), path) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::read_zipper_at(lit, path) {
                            Ok(z) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(z)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PWriteZipper . m:Proc
        |- m "." "writeZipper" "(" ")" : Proc ![{
            match &m {
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::write_zipper_root(lit) {
                            Ok(z) => Proc::CastWriteZipper(std::sync::Arc::new(WriteZipper::Lit(std::sync::Arc::new(z)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        PWriteZipperAt . m:Proc, p:Proc
        |- m "." "writeZipperAt" "(" p ")" : Proc ![{
            match (&m, &p) {
                (Proc::CastPathmap(inner), path) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref lit) => {
                        match crate::rholang::zipper::write_zipper_at(lit, path) {
                            Ok(z) => Proc::CastWriteZipper(std::sync::Arc::new(WriteZipper::Lit(std::sync::Arc::new(z)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── ReadZipper methods ───────────────────────────────────────────
        RZGetLeaf . z:Proc
        |- z "." "getLeaf" "(" ")" : Proc ![{
            // Failed navigation STAYS STUCK (user decision 2026-06-30): leave the
            // unreduced `z.getLeaf()` node rather than rewriting to `error`. The
            // closure captures the OUTER operand `z` (the inner `z` shadow below is
            // the ReadZipperLit, used only for the nav call).
            let stuck = || Proc::RZGetLeaf(std::sync::Arc::new(z.clone()));
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_get_leaf(z.as_ref()) {
                        Ok(mettail_runtime::PathValue::Set(v)) => v,
                        // ★★ #74, RULED 2026-07-29 (USER) — the ZIPPER SIBLING of
                        // `MGet`'s unset arm, and the second of exactly TWO
                        // value-reading pathmap surfaces.
                        //
                        // The leaf EXISTS but nothing is stored under it
                        // (`{| k |}`). No reduction of `getLeaf()` can produce a
                        // value that was never written, so this ERRS rather than
                        // blocking — a stuck term would promise a future state
                        // that does not exist. Same ruling, same reasoning, same
                        // departure from the `MSet` precedent as `MGet` above.
                        //
                        // ⚠ NOTE THE ASYMMETRY WITH THE ARM BELOW, which is
                        // deliberate and is exactly the distinction the ruling
                        // turns on: a FAILED NAVIGATION (`Err(())` — there is no
                        // leaf here at all) stays STUCK, because a later
                        // reduction of the zipper expression really can move the
                        // focus somewhere that has a leaf. A leaf that exists
                        // and holds nothing cannot become non-empty.
                        Ok(mettail_runtime::PathValue::Unset) => {
                            #[cfg(debug_assertions)]
                            eprintln!(
                                "[readZipper.getLeaf] the leaf at this focus has no value, \
                                 so `getLeaf()` has nothing to return — the leaf IS \
                                 present. An unset value is not `Nil` and not absent.",
                            );
                            Proc::Err
                        },
                        Err(()) => stuck(),
                    },
                    _ => stuck(),
                },
                _ => stuck(),
            }
        }] fold;

        RZDescendTo . z:Proc, rel:Proc
        |- z "." "descendTo" "(" rel ")" : Proc ![{
            match (&z, &rel) {
                (Proc::CastReadZipper(inner), rel) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_descend_to(z.as_ref(), rel) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        RZChildCount . z:Proc
        |- z "." "childCount" "(" ")" : Proc ![{
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_child_count(z.as_ref()) {
                        Ok(n) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(n))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        RZDescendFirst . z:Proc
        |- z "." "descendFirst" "(" ")" : Proc ![{
            // Failed navigation STAYS STUCK (user decision 2026-06-30).
            let stuck = || Proc::RZDescendFirst(std::sync::Arc::new(z.clone()));
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_descend_first(z.as_ref()) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => stuck(),
                    },
                    _ => stuck(),
                },
                _ => stuck(),
            }
        }] fold;

        RZToNextSibling . z:Proc
        |- z "." "toNextSibling" "(" ")" : Proc ![{
            // Failed navigation STAYS STUCK (user decision 2026-06-30).
            let stuck = || Proc::RZToNextSibling(std::sync::Arc::new(z.clone()));
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_to_next_sibling(z.as_ref()) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => stuck(),
                    },
                    _ => stuck(),
                },
                _ => stuck(),
            }
        }] fold;

        RZToPrevSibling . z:Proc
        |- z "." "toPrevSibling" "(" ")" : Proc ![{
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_to_prev_sibling(z.as_ref()) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        RZDescendIndexedBranch . z:Proc, i:Proc
        |- z "." "descendIndexedBranch" "(" i ")" : Proc ![{
            // The branch index `i` is a rholang integer literal, which lexes to
            // `BigInt` (see RZAscend). Accept both `CastBigInt` and `CastInt` via
            // `proc_to_index` so the merged grammar reduces (this op was
            // merge-added from `main`, where the literal would have been
            // `CastInt`).
            match (&z, crate::rholang::zipper::proc_to_index(&i)) {
                (Proc::CastReadZipper(inner), Some(n)) => match inner.as_ref() {
                    ReadZipper::Lit(z) => {
                        match crate::rholang::zipper::zipper_descend_indexed_branch(z.as_ref(), n) {
                            Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        RZAscendOne . z:Proc
        |- z "." "ascendOne" "(" ")" : Proc ![{
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_ascend_one(z.as_ref()) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        RZAscend . z:Proc, n:Proc
        |- z "." "ascend" "(" n ")" : Proc ![{
            // The step count `n` is a rholang integer literal. Bare integers in
            // rholang lex to `BigInt` (Rholang 1.4 arbitrary-precision default),
            // so `n` arrives as `Proc::CastBigInt(NumLit)` — NOT `Proc::CastInt`.
            // This op was merge-added from `main`, whose integer literals were
            // `CastInt`; `proc_to_index` accepts BOTH forms so the merged grammar
            // reduces instead of falling through to `Proc::Err`.
            match (&z, crate::rholang::zipper::proc_to_index(&n)) {
                (Proc::CastReadZipper(inner), Some(steps)) => match inner.as_ref() {
                    ReadZipper::Lit(z) => {
                        match crate::rholang::zipper::zipper_ascend(z.as_ref(), steps) {
                            Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── ReadZipper ENUMERATION ───────────────────────────────────────
        //
        // These three make walking a `Pathmap` TOTAL: descend to a leaf, read
        // its key and its value, advance to the next leaf, and know the count
        // in advance. Each SURFACES capability the `pathmap` crate already has
        // — `ZipperMoving::path()`, `ZipperIteration::to_next_val()`, and
        // `ZipperMoving::val_count()` respectively; the implementations are in
        // `crate::rholang::zipper`, which carries the full rationale.
        //
        // ## Why enumeration is LEAF-granular and not built from the moves above
        //
        // A `Pathmap` key is a LIST of segments, and `flatten_segments` encodes
        // it across many trie BYTES (`[1,2,3]` ▸ `31 FF 32 FF 33 FF`). Every
        // move declared above — `descendFirst`, `toNextSibling`,
        // `toPrevSibling`, `descendIndexedBranch`, `ascend` — steps exactly ONE
        // BYTE, parking the focus MID-SEGMENT, where `getLeaf()` is stuck (no
        // value lives there) and `getSubtrie()` FAILS (the relative keys below
        // it open with a partial segment that no `Proc` can name).
        //
        // And Rholang surface syntax cannot ADDRESS a byte: `descendTo` takes a
        // `Proc` and always encodes a whole segment. So the byte-granular moves
        // cannot be composed into an enumeration FROM SOURCE at any arity, and
        // adding a cursor-key accessor beside them would not have closed the
        // gap. `toNextLeaf` sidesteps the granularity mismatch entirely by
        // landing only on positions that carry a value — every one of which is
        // a complete, segment-aligned, decodable key, so the `getPath()` and
        // `getLeaf()` at each stop are BOTH guaranteed to reduce.
        //
        // The walk, whose bound is decidable and whose every step is total:
        //
        //     z <- m.readZipper() ;  n <- z.leafCount() ;
        //     n x ( z <- z.toNextLeaf() ;  use z.getPath(), z.getLeaf() )
        //
        // Scoping an enumeration is served ALGEBRAICALLY instead:
        // `m.getSubtrieAt(p).readZipper()` walks exactly the branch at `p`.

        RZGetPath . z:Proc
        |- z "." "getPath" "(" ")" : Proc ![{
            // THE CURSOR KEY. Failed readout STAYS STUCK (user decision
            // 2026-06-30), matching `RZGetLeaf`. Errors only at the trie root,
            // which names no entry.
            let stuck = || Proc::RZGetPath(std::sync::Arc::new(z.clone()));
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_get_path(z.as_ref()) {
                        Ok(p) => p,
                        Err(()) => stuck(),
                    },
                    _ => stuck(),
                },
                _ => stuck(),
            }
        }] fold;

        RZToNextLeaf . z:Proc
        |- z "." "toNextLeaf" "(" ")" : Proc ![{
            // ⚠ EXHAUSTION STAYS STUCK, AND MUST. `to_next_val()` resets the
            // zipper to the ROOT when it runs out, so a rewrite that returned
            // that zipper would restart the walk forever with no error raised
            // anywhere. The reducer reports this same condition as `Nil`; C1
            // must translate `Nil` back to THIS stuck form. See the
            // CROSS-ENDPOINT CONTRACT block in `crate::rholang::zipper`.
            let stuck = || Proc::RZToNextLeaf(std::sync::Arc::new(z.clone()));
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_to_next_leaf(z.as_ref()) {
                        Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                        Err(()) => stuck(),
                    },
                    _ => stuck(),
                },
                _ => stuck(),
            }
        }] fold;

        RZLeafCount . z:Proc
        |- z "." "leafCount" "(" ")" : Proc ![{
            // Values AT AND BELOW the focus: the map's cardinality at the root,
            // the branch's result count at a prefix — and the DECIDABLE BOUND
            // that terminates a `toNextLeaf` walk. Mirrors `RZChildCount`'s
            // `Proc::Err` convention (a count is not a navigation).
            match &z {
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rholang::zipper::zipper_leaf_count(z.as_ref()) {
                        Ok(n) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(n))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── WriteZipper methods ──────────────────────────────────────────
        WZSetLeaf . w:Proc, full:Proc, v:Proc
        |- w "." "setLeaf" "(" full "," v ")" : Proc ![{
            match (&w, &full, &v) {
                (Proc::CastWriteZipper(inner), fp, val) => match inner.as_ref() {
                    WriteZipper::Lit(z) => {
                        // #74: `setLeaf` binds a value, so it is explicitly
                        // `Set(v)`; no surface operation writes an `Unset`.
                        match crate::rholang::zipper::write_zipper_set_leaf(
                            z.as_ref(),
                            fp,
                            mettail_runtime::PathValue::Set((*val).clone()),
                        ) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        WZSetSubtrie . w:Proc, rel:Proc
        |- w "." "setSubtrie" "(" rel ")" : Proc ![{
            match (&w, &rel) {
                (Proc::CastWriteZipper(inner), Proc::CastPathmap(pm)) => match (inner.as_ref(), pm.as_ref()) {
                    (WriteZipper::Lit(z), Pathmap::PathmapLit(rel_lit)) => {
                        match crate::rholang::zipper::write_zipper_set_subtrie(z.as_ref(), rel_lit) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        WZRemoveLeaf . w:Proc
        |- w "." "removeLeaf" "(" ")" : Proc ![{
            match &w {
                Proc::CastWriteZipper(inner) => match inner.as_ref() {
                    WriteZipper::Lit(z) => match crate::rholang::zipper::write_zipper_remove_leaf(z.as_ref()) {
                        Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                        Err(()) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        WZRemoveBranches . w:Proc
        |- w "." "removeBranches" "(" ")" : Proc ![{
            match &w {
                Proc::CastWriteZipper(inner) => match inner.as_ref() {
                    WriteZipper::Lit(z) => {
                        match crate::rholang::zipper::write_zipper_remove_branches(z.as_ref()) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        WZGraft . w:Proc, rz:Proc
        |- w "." "graft" "(" rz ")" : Proc ![{
            match (&w, &rz) {
                (Proc::CastWriteZipper(wi), Proc::CastReadZipper(ri)) => match (wi.as_ref(), ri.as_ref()) {
                    (WriteZipper::Lit(z), ReadZipper::Lit(src)) => {
                        match crate::rholang::zipper::write_zipper_graft(z.as_ref(), src.as_ref()) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        WZJoinInto . w:Proc, rz:Proc
        |- w "." "joinInto" "(" rz ")" : Proc ![{
            match (&w, &rz) {
                (Proc::CastWriteZipper(wi), Proc::CastReadZipper(ri)) => match (wi.as_ref(), ri.as_ref()) {
                    (WriteZipper::Lit(z), ReadZipper::Lit(src)) => {
                        match crate::rholang::zipper::write_zipper_join_into(z.as_ref(), src.as_ref()) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        // ── Set methods ────────────────────────────────────────────────────
        SAdd . set_proc:Proc, e:Proc
        |- set_proc "." "add" "(" e ")" : Proc ![{
            match &set_proc {
                Proc::CastSet(inner) => match inner.as_ref() {
                    Set::SetLit(ref payload) => {
                        let mut new_set = payload.clone();
                        new_set.insert(crate::rholang::runtime::normalize_collection_element(&e));
                        Proc::CastSet(std::sync::Arc::new(Set::SetLit(new_set)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }
        }] fold;

        Not . a:Proc |- "not" a : Proc ![
            { match &a {
                Proc::CastBool(b) => match &**b {
                    Bool::BoolLit(v) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!v))),
                    _ => Proc::Err,
                },
                // See `runtime::is_ground_operand`: `error` only for a ground operand.
                _ => crate::rholang::runtime::unary_fallback(a, || {
                    Proc::Not(std::sync::Arc::new(a.clone()))
                }),
            }}
        ] fold;

        ToBool . p:Proc |- "bool" "(" p ")" : Proc ![
            { match &p {
                Proc::CastBool(x) => Proc::CastBool(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*i != 0))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*u != 0))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!n.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!r.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(f.get() != 0.0))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!Zero::is_zero(fp.unscaled())))),
                    _ => Proc::Err,
                },
                // ★ A FAILED PARSE IS AN ERROR, NEVER THE VALUE `false` (2026-07-26).
                //
                // This arm used to read `s.parse::<bool>().unwrap_or(false)`. Rust's
                // `FromStr for bool` accepts only the two spellings `"true"` and `"false"`,
                // so `bool("True")`, `bool("1")`, `bool("yes")` and `bool("")` all folded to
                // the VALUE `false` — indistinguishable, at every consumer, from a string
                // that really did spell `false`.
                //
                // That is the fabrication this file's own convention forbids: the governing
                // rule at `rholang/runtime.rs` and restated on the boolean operators above is
                // *"A failed operator must never invent a value — hence `Proc::Err`, never a
                // fabricated `BoolLit`."* Every sibling arm in this very `match` already
                // answers `Proc::Err`; this one was the outlier.
                //
                // It matters more here than at a typical operator because `bool(...)` feeds
                // the GUARD lane: a fabricated `false` is a fabricated guard verdict, and a
                // guard verdict decides whether a COMM fires.
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => match s.parse::<bool>() {
                        Ok(v) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(v))),
                        Err(_) => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToStr . p:Proc |- "str" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(x) => Proc::CastStr(x.clone()),
                Proc::CastInt(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastUInt32(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBigInt(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBigRat(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastFloat(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastFixed(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBool(x) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(x.as_ref().eval().to_string()))),
                _ => Proc::Err,
            }}
        ] fold;

        // L9-5: FLT guest-body captures. Each `*flt(node, open, close)` consumes a
        // delimited foreign-language region and assembles an opaque native
        // `FltNode { tag, body_src, holes[{name,category,offset}], position }` (an
        // inert BoundTerm leaf). The three forms differ ONLY in surface delimiter;
        // all carry the same `Arc<FltNode>` payload. Reduction is deferred to L9-6
        // (`lower_proc`'s `PFlt` arm → `FltResolver`); until an FLT resolver is
        // installed a `PFlt` is inert (empty-resolver default = zero behavior
        // change), so no `eval` disposition is declared. Declared LAST so the
        // existing Proc rule indices (and the pinned @/mixfix cohort structure)
        // are unperturbed — a leading-capture rule joins no infix/mixfix cohort.
        PFlt . |- *flt(node, FltOpenBacktick, FltCloseBacktick) : Proc;
        PFltFence . |- *flt(node, FltOpenFence, FltCloseFence) : Proc;
        PFltBrace . |- *flt(node, FltOpenBrace, FltCloseBrace) : Proc;

        // ★ THE LOOKAHEAD SUFFIX — `P[n]` and `P[*]` (FIPS `2026-01-08-Lookahead`).
        //
        // `x!(P)[*]` evaluates `P` speculatively along ALL execution paths, gathers each
        // branch's terminal state into a `success` map keyed by the TRACE (the sequence of
        // scheduling choices), aborted paths into `failure`, and truncated-but-resumable
        // paths into `truncated`; `x!(P)[n]` is the same exploration bounded to `n` steps,
        // where a step is one COMM. Both deliver their maps on `x`.
        //
        // ## Why two rules and not one with an optional operand
        //
        // `*` is a LITERAL here, not a parameter: `p "[" "*" "]"` and `p "[" n "]"` are
        // distinct surfaces, and the spec's `terms` block has no category-less production
        // (every rule ends `: Category`), so a shared `LookaheadSuffix` nonterminal is not
        // expressible. Two `: Proc` rules is the spec-conformant encoding.
        //
        // ## Why the operand is `p:Proc` and not a dedicated `Send` category
        //
        // The ~20 send sugars are all `: Proc` — there is no shared `Send` nonterminal to
        // attach a suffix to. Taking `p:Proc` attaches the suffix uniformly to every send
        // form at once, and the LOWERING (`rholang_ast.rs`) is where a non-send operand is
        // rejected — with a typed error naming what it got, never silently.
        //
        // ## Ambiguity: measured, not assumed
        //
        // `"["`/`"]"` are otherwise ONLY the `List` type's `open_parts`/`close_parts`, so
        // these rules share a surface with list literals and with an indexing-shaped read.
        // `languages/tests/x2_lookahead_bracket_probe.rs` is the regression net: over 17
        // inputs it establishes that both rules parse unambiguously, that `[1]` still reads
        // as a list, that `[*x]` still reads as a list of a dereference, and that no
        // previously-accepted string changes meaning — with a TEETH control (a deliberately
        // duplicated production) proving the reading counter can see ambiguity at all.
        //
        // Declared LAST, after the FLT captures, so the existing Proc rule indices and the
        // pinned @/mixfix cohort structure ahead of them are unperturbed.
        PLookahead . p:Proc, n:Proc |- p "[" n "]" : Proc;
        PLookaheadAll . p:Proc |- p "[" "*" "]" : Proc;
    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;

        Extrude . xs.*map(|x| x # ...rest)
            |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest})) ;
    },

    rewrites {

        // Communication for `PForUser` (single- and multi-`&` receive rows) lives in
        // `receive::try_comm_rw_proc` plus a custom `rw_proc` rule in the logic block below.

        Exec . |- (PDrop (NQuote P)) ~> P;
        ExecQuoteShort . |- (PDrop (NQuoteShort P)) ~> P;
        ExecParenQuote . |- (PDrop (NParen (NQuote P))) ~> P;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);

        // TODO: shorthand to make these in the term declarations
        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);

        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);

        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);

        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);

        MulCongL . | S ~> T |- (Mul S X) ~> (Mul T X);

        MulCongR . | S ~> T |- (Mul X S) ~> (Mul X T);

        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);

        DivCongR . | S ~> T |- (Div X S) ~> (Div X T);

        ModCongL . | S ~> T |- (Mod S X) ~> (Mod T X);

        ModCongR . | S ~> T |- (Mod X S) ~> (Mod X T);

        NegIntCong . | S ~> T |- (NegInt S) ~> (NegInt T);
        NegProcCong . | S ~> T |- (NegProc S) ~> (NegProc T);

        BitAndCongL . | S ~> T |- (BitAnd S X) ~> (BitAnd T X);

        BitAndCongR . | S ~> T |- (BitAnd X S) ~> (BitAnd X T);

        BitOrCongL . | S ~> T |- (BitOr S X) ~> (BitOr T X);

        BitOrCongR . | S ~> T |- (BitOr X S) ~> (BitOr X T);

        BitNotCong . | S ~> T |- (BitNot S) ~> (BitNot T);

        EqCongL . | S ~> T |- (Eq S X) ~> (Eq T X);
        EqCongR . | S ~> T |- (Eq X S) ~> (Eq X T);
        NeCongL . | S ~> T |- (Ne S X) ~> (Ne T X);
        NeCongR . | S ~> T |- (Ne X S) ~> (Ne X T);
        GtCongL . | S ~> T |- (Gt S X) ~> (Gt T X);
        GtCongR . | S ~> T |- (Gt X S) ~> (Gt X T);
        LtCongL . | S ~> T |- (Lt S X) ~> (Lt T X);
        LtCongR . | S ~> T |- (Lt X S) ~> (Lt X T);
        GtEqCongL . | S ~> T |- (GtEq S X) ~> (GtEq T X);
        GtEqCongR . | S ~> T |- (GtEq X S) ~> (GtEq X T);
        LtEqCongL . | S ~> T |- (LtEq S X) ~> (LtEq T X);
        LtEqCongR . | S ~> T |- (LtEq X S) ~> (LtEq X T);

        NotCong . | S ~> T |- (Not S) ~> (Not T);
        AndCongL . | S ~> T |- (And S X) ~> (And T X);
        AndCongR . | S ~> T |- (And X S) ~> (And X T);
        OrCongL . | S ~> T |- (Or S X) ~> (Or T X);
        OrCongR . | S ~> T |- (Or X S) ~> (Or X T);

        LLengthCong . | S ~> T |- (LLength S) ~> (LLength T);

        MGetCongL . | S ~> T |- (MGet S X) ~> (MGet T X);
        MGetCongR . | S ~> T |- (MGet X S) ~> (MGet X T);
        MSetCongL . | S ~> T |- (MSet S K V) ~> (MSet T K V);
        MSetCongKey . | S ~> T |- (MSet M S V) ~> (MSet M T V);
        MSetCongVal . | S ~> T |- (MSet M K S) ~> (MSet M K T);
        MContainsCongL . | S ~> T |- (MContains S X) ~> (MContains T X);
        MContainsCongR . | S ~> T |- (MContains X S) ~> (MContains X T);
        MDeleteCongL . | S ~> T |- (MDelete S X) ~> (MDelete T X);
        MDeleteCongR . | S ~> T |- (MDelete X S) ~> (MDelete X T);
        MUnionCongL . | S ~> T |- (MUnion S X) ~> (MUnion T X);
        MUnionCongR . | S ~> T |- (MUnion X S) ~> (MUnion X T);
        MSizeCong . | S ~> T |- (MSize S) ~> (MSize T);
        MToByteArrayCong . | S ~> T |- (MToByteArray S) ~> (MToByteArray T);
        MKeysCong . | S ~> T |- (MKeys S) ~> (MKeys T);
        MValuesCong . | S ~> T |- (MValues S) ~> (MValues T);

        LNthCongL . | S ~> T |- (LNth S X) ~> (LNth T X);
        LNthCongR . | S ~> T |- (LNth X S) ~> (LNth X T);
        // `LLast` is unary, so it takes one congruence — the same shape `LLengthCong` takes.
        // Without it a receiver that is itself a redex (`[1,2].concat([3,4]).last()`) could never
        // reduce to the list the fold body needs.
        LLastCong . | S ~> T |- (LLast S) ~> (LLast T);
        LConcatCongL . | S ~> T |- (LConcat S X) ~> (LConcat T X);
        LConcatCongR . | S ~> T |- (LConcat X S) ~> (LConcat X T);

        BCountCongL . | S ~> T |- (BCount S X) ~> (BCount T X);
        BCountCongR . | S ~> T |- (BCount X S) ~> (BCount X T);
        BDiffCongL . | S ~> T |- (BDiff S X) ~> (BDiff T X);
        BDiffCongR . | S ~> T |- (BDiff X S) ~> (BDiff X T);
        BRemoveCongL . | S ~> T |- (BRemove S X) ~> (BRemove T X);
        BRemoveCongR . | S ~> T |- (BRemove X S) ~> (BRemove X T);

        PRestrictCongL . | S ~> T |- (PRestrict S X) ~> (PRestrict T X);
        PRestrictCongR . | S ~> T |- (PRestrict X S) ~> (PRestrict X T);
        PSubtractCongL . | S ~> T |- (PSubtract S X) ~> (PSubtract T X);
        PSubtractCongR . | S ~> T |- (PSubtract X S) ~> (PSubtract X T);
        PMeetCongL . | S ~> T |- (PMeet S X) ~> (PMeet T X);
        PMeetCongR . | S ~> T |- (PMeet X S) ~> (PMeet X T);
        PGetSubtrieCong . | S ~> T |- (PGetSubtrie S) ~> (PGetSubtrie T);
        PGetSubtrieAtCongL . | S ~> T |- (PGetSubtrieAt S X) ~> (PGetSubtrieAt T X);
        PGetSubtrieAtCongR . | S ~> T |- (PGetSubtrieAt X S) ~> (PGetSubtrieAt X T);
        PReadZipperCong . | S ~> T |- (PReadZipper S) ~> (PReadZipper T);
        PReadZipperAtCongL . | S ~> T |- (PReadZipperAt S X) ~> (PReadZipperAt T X);
        PReadZipperAtCongR . | S ~> T |- (PReadZipperAt X S) ~> (PReadZipperAt X T);
        PWriteZipperCong . | S ~> T |- (PWriteZipper S) ~> (PWriteZipper T);
        PWriteZipperAtCongL . | S ~> T |- (PWriteZipperAt S X) ~> (PWriteZipperAt T X);
        PWriteZipperAtCongR . | S ~> T |- (PWriteZipperAt X S) ~> (PWriteZipperAt X T);

        RZGetLeafCong . | S ~> T |- (RZGetLeaf S) ~> (RZGetLeaf T);
        RZDescendToCongL . | S ~> T |- (RZDescendTo S X) ~> (RZDescendTo T X);
        RZDescendToCongR . | S ~> T |- (RZDescendTo X S) ~> (RZDescendTo X T);
        RZChildCountCong . | S ~> T |- (RZChildCount S) ~> (RZChildCount T);
        RZDescendFirstCong . | S ~> T |- (RZDescendFirst S) ~> (RZDescendFirst T);
        RZToNextSiblingCong . | S ~> T |- (RZToNextSibling S) ~> (RZToNextSibling T);
        RZToPrevSiblingCong . | S ~> T |- (RZToPrevSibling S) ~> (RZToPrevSibling T);
        RZDescendIndexedBranchCongL . | S ~> T |- (RZDescendIndexedBranch S X) ~> (RZDescendIndexedBranch T X);
        RZDescendIndexedBranchCongR . | S ~> T |- (RZDescendIndexedBranch X S) ~> (RZDescendIndexedBranch X T);
        RZAscendOneCong . | S ~> T |- (RZAscendOne S) ~> (RZAscendOne T);
        RZAscendCongL . | S ~> T |- (RZAscend S X) ~> (RZAscend T X);
        RZAscendCongR . | S ~> T |- (RZAscend X S) ~> (RZAscend X T);

        WZSetLeafCongL . | S ~> T |- (WZSetLeaf S X Y) ~> (WZSetLeaf T X Y);
        WZSetLeafCongKey . | S ~> T |- (WZSetLeaf M S Y) ~> (WZSetLeaf M T Y);
        WZSetLeafCongVal . | S ~> T |- (WZSetLeaf M K S) ~> (WZSetLeaf M K T);
        WZSetSubtrieCongL . | S ~> T |- (WZSetSubtrie S X) ~> (WZSetSubtrie T X);
        WZSetSubtrieCongR . | S ~> T |- (WZSetSubtrie X S) ~> (WZSetSubtrie X T);
        WZRemoveLeafCong . | S ~> T |- (WZRemoveLeaf S) ~> (WZRemoveLeaf T);
        WZRemoveBranchesCong . | S ~> T |- (WZRemoveBranches S) ~> (WZRemoveBranches T);
        WZGraftCongL . | S ~> T |- (WZGraft S X) ~> (WZGraft T X);
        WZGraftCongR . | S ~> T |- (WZGraft X S) ~> (WZGraft X T);
        WZJoinIntoCongL . | S ~> T |- (WZJoinInto S X) ~> (WZJoinInto T X);
        WZJoinIntoCongR . | S ~> T |- (WZJoinInto X S) ~> (WZJoinInto X T);

        CastMapCong . | S ~> T |- (CastMap S) ~> (CastMap T);
        CastSetCong . | S ~> T |- (CastSet S) ~> (CastSet T);
        CastPathmapCong . | S ~> T |- (CastPathmap S) ~> (CastPathmap T);
        CastReadZipperCong . | S ~> T |- (CastReadZipper S) ~> (CastReadZipper T);
        CastWriteZipperCong . | S ~> T |- (CastWriteZipper S) ~> (CastWriteZipper T);
        SAddCongL . | S ~> T |- (SAdd S X) ~> (SAdd T X);
        SAddCongR . | S ~> T |- (SAdd X S) ~> (SAdd X T);
        CastIntCong . | S ~> T |- (CastInt S) ~> (CastInt T);
        CastUInt32Cong . | S ~> T |- (CastUInt32 S) ~> (CastUInt32 T);
        CastBigIntCong . | S ~> T |- (CastBigInt S) ~> (CastBigInt T);
        CastBigRatCong . | S ~> T |- (CastBigRat S) ~> (CastBigRat T);
        CastFixedCong . | S ~> T |- (CastFixed S) ~> (CastFixed T);
        FractionProcCongL . | S ~> T |- (FractionProc S X) ~> (FractionProc T X);
        FractionProcCongR . | S ~> T |- (FractionProc X S) ~> (FractionProc X T);
        IntBinProcCongL . | S ~> T |- (IntBinProc S R) ~> (IntBinProc T R);
        IntBinProcCongR . | S ~> T |- (IntBinProc L S) ~> (IntBinProc L T);
        UIntBinProcCongL . | S ~> T |- (UIntBinProc S R) ~> (UIntBinProc T R);
        UIntBinProcCongR . | S ~> T |- (UIntBinProc L S) ~> (UIntBinProc L T);
        FloatBinProcCongL . | S ~> T |- (FloatBinProc S R) ~> (FloatBinProc T R);
        FloatBinProcCongR . | S ~> T |- (FloatBinProc L S) ~> (FloatBinProc L T);
        FixedBinProcCongL . | S ~> T |- (FixedBinProc S R) ~> (FixedBinProc T R);
        FixedBinProcCongR . | S ~> T |- (FixedBinProc L S) ~> (FixedBinProc L T);
        BigintCastProcCong . | S ~> T |- (BigintCastProc S) ~> (BigintCastProc T);
        BigratCastProcCong . | S ~> T |- (BigratCastProc S) ~> (BigratCastProc T);
        ToBoolCong . | S ~> T |- (ToBool S) ~> (ToBool T);
        ToStrCong . | S ~> T |- (ToStr S) ~> (ToStr T);
    },

    logic {
        // Normalize polyadic send sugar `x!(a, b, ...)` to unary send with list payload.
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::POutput2Plus(ref n, ref a, ref bs) = s,
            let res = {
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.as_ref().clone());
                items.extend(bs.iter().cloned());
                Proc::POutput(
                    std::sync::Arc::new(n.as_ref().clone()),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            };
        // Normalize polyadic persistent send sugar `x!!(a, b, ...)` similarly.
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::PPersistOutput2Plus(ref n, ref a, ref bs) = s,
            let res = {
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.as_ref().clone());
                items.extend(bs.iter().cloned());
                Proc::PPersistOutput(
                    std::sync::Arc::new(n.as_ref().clone()),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            };

        // fold *(@(P)) to P so that remove(*(@(bag)), *(@(elem))) can reduce (Exec semantics in fold)
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::PDrop(ref n) = s,
            if let Name::NQuote(ref p) = n.as_ref(),
            let res = p.as_ref().clone();

        // Ensure bare infix parallel reaches canonical PPar during execution so COMM can fire.
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::PParInfix(ref a, ref b) = s,
            let res = crate::rholang::runtime::merge_pp_parallel(a.as_ref().clone(), b.as_ref().clone());

        // Evaluate guarded communication helper introduced by CommPatternWhere.
        // This bridges rewrite-time construction (`CommWhere ...`) to runtime semantics:
        // - successful match + true guard => reduced body
        // - mismatch / false guard => original receive+send pair (identity)
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::CommWhere(ref pat, ref n, ref q, ref cond, ref body) = s,
            let res = crate::rholang::receive::comm_pforwhere_subst(
                pat.as_ref(),
                n.as_ref(),
                q.as_ref(),
                cond.as_ref(),
                body.as_ref(),
            );

        // Desugar `!?` query binds inside `PForUser` (parse may leave `InputBindQuery` in rows; idempotent).
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::PForUser(ref rows, ref body) = s,
            if crate::rholang::receive::pfor_user_still_has_query_rows(rows),
            let res = crate::rholang::receive::desugar_for_rows(rows.clone(), body.as_ref());

        // `PForUser` communication (replaces declarative Comm* rewrites on `PFor` / `PForWhere` / `PForJoin`).
        rw_proc(s0.clone(), res) <--
            eq_proc(s0, s),
            if let Some(rewritten) = crate::rholang::receive::try_comm_rw_proc(&s),
            if !rewritten.term_eq(&s),
            if !rewritten.term_eq(&s0),
            let res = rewritten;

        // many-step to a result
        relation path(Proc, Proc);
        path(p0, p1) <-- fold_proc(p0, p1);
        path(p0, p1) <-- rw_proc(p0, p1);
        path(p0, p2) <-- path(p0, p1), path(p1, p2);

        // or we can store every step!
        relation path_vec(Vec<Proc>);
        path_vec(xs) <--
            proc(x0), rw_proc(x0,x1),
            if x0 != x1,
            let xs = vec![x0.clone(), x1.clone()];
        path_vec(zs) <--
            path_vec(xs), path_vec(ys),
            if xs.last() == ys.first(),
            let zs = [xs.as_slice(), ys.as_slice()].concat();

        // paths where term size (display length) strictly decreases at every step
        // TODO: currently makes execution slow; investigate why
        // relation shrinking_path(Vec<Proc>);
        // shrinking_path(xs) <--
        //     path_vec(xs),
        //     if xs.windows(2).all(|w| w[0].to_string().len() > w[1].to_string().len());

        // context-labelled transition system:
        // p -c-> q if c(p)~>q
        relation trans(Proc, Proc, Proc);
        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(std::sync::Arc::new(c.clone()), std::sync::Arc::new(p.clone())),
            let res = app.normalize(),
            path(res.clone(), q);

        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(std::sync::Arc::new(c.clone()), vec![p.clone()]),
            let res = app.normalize(),
            path(res.clone(), q);

        // contexts for testing (TODO: auto-generate)
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

        // rules to add c(p) to the set of processes
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(std::sync::Arc::new(c.clone()), std::sync::Arc::new(p.clone())),
            let res = app.normalize();
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(std::sync::Arc::new(c.clone()), vec![p.clone()]),
            let res = app.normalize();
    },
}
