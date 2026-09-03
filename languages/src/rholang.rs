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
        // Only spellings introduced by the DDL, plus the explicit `PPar`
        // constructor-label exception, retain an identifier co-reading here.
        // `in` is an inherited fixed Rholang binder-list terminator and is also
        // fixed in DDL `let`; contextualizing it changes the legacy token DAG.
        contextual_keywords: [
            "Module", "Theory", "theory", "import", "as", "from", "Empty",
            "free", "let", "Types", "Exports", "Replacements", "Terms",
            "Equations", "Rewrites", "Data", "HashBag", "Set", "List", "sep",
            "subst", "PPar",
        ],
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
        // URI literals are binder annotations, not string-valued processes.
        // `Uri` is intentionally not a native string category: its sole
        // constructor captures the declared UriLiteral token verbatim, keeping
        // URI syntax disjoint from GString and from modal FLT backticks.
        Uri
        // ★★ `Bytes` IS A BYTE ARRAY, NOT A STRING — LANDED 2026-07-30 (ruled 2026-07-29).
        //
        // This was `![String] as Bytes`. Both `Str` and `Bytes` were therefore STRING-SHAPED, so
        // the generator emitted a `StringLit` variant for each and a `"…"` literal satisfied
        // BOTH — every string literal in the language had two readings, `CastStr` and
        // `CastBytes`. That was not an election between two designed alternatives; the
        // DECLARATION created the ambiguity, and the disambiguator was left to clean it up.
        //
        // Upstream has no such ambiguity, and cannot express one:
        //
        //   * the wire model (`RhoTypes.proto:230-232`) has TWO DISTINCT CARRIERS —
        //     `string g_string = 3` and `bytes g_byte_array = 25`;
        //   * the grammar (`rholang-tree-sitter/grammar.js`) has NO byte-array literal: the
        //     ground-literal choice at `:435-436` is `string_literal` and `uri_literal` ONLY, and
        //     `ByteArray` appears at `:424` solely as a TYPE NAME in `simple_type` — usable in
        //     `matches`/type patterns and produced by builtins, never written as a literal.
        //
        // So a `"…"` literal is a `GString` upstream, full stop. With the `Vec<u8>` carrier it is
        // a `Str` HERE BY CONSTRUCTION: the ambiguity is UNSPELLABLE rather than elected — no
        // disambiguator pin, no dependence on rule declaration order. The `Bytes` category's own
        // literal variant is now `Bytes::BytesLit(Vec<u8>)`, which no `"…"` token can inhabit.
        //
        // ── WHAT THIS WAITED ON, AND WHAT UNBLOCKED IT ──────────────────────────────────────
        //
        // The carrier change was implemented and measured on 2026-07-29 and HELD (`2eebf722`),
        // because it left `Bytes` with NO SURFACE FORM AT ALL — not merely "no literal", which is
        // upstream's position, but nothing RENDERABLE either. MEASURED then:
        //
        //     gen_rholang_prop::bytes_display_parse_roundtrip
        //       arb_bytes produced unparseable surface term ""
        //
        // — eleven failures, because a `Vec<u8>` payload is not string-shaped (so no `StringLit`
        // arm) and `Bytes` declares no collection delimiters (so the collection Display arm wrapped
        // its bytes in EMPTY open/close). A `Bytes` value was constructible in Rust and could not
        // be written or printed. That is a broken Display→parse invariant for a whole category,
        // not a test artefact, and suppressing the generated rows would have hidden it.
        //
        // The missing surface is the `b"…"` literal declared in `literals { Bytes { … } }` below,
        // ruled 2026-07-29 after asking how C++ spells a byte literal: **`b"deadbeef"`, via
        // `LiteralFamily::Custom`**. Two of the arguments made for a different spelling were WRONG
        // and are recorded so they are not restored:
        //
        //   ✗ `0x…` on upstream-alignment grounds. INVERTED: mettail already spends `0x…` on
        //     THREE hex integer forms (`Int`, `BigInt`, `BigRat` radix patterns), and upstream
        //     Rholang has ZERO `0x…` syntax. `0x…` is refuted.
        //   ✗ "the faithful shape is a builtin plus a type pattern, NOT a literal" (written in
        //     `2eebf722`). It answers the wrong question: builtins give a byte array a
        //     PRODUCER, and what was missing is a SURFACE — something `Display` can write and the
        //     parser can read back. Upstream itself demonstrates the gap: its pretty-printer
        //     ALREADY prints a byte array (`pretty_printer.rs:2860`, `hex::encode(bs)`) and its
        //     own grammar cannot read that back. `b"…"` prints the same hex digits inside a frame
        //     that parses. Fixing an upstream bug is BUG FIX, never DIVERGENT.
        //
        // ── WHAT THE CARRIER CHANGE DELIVERS ───────────────────────────────────────────────
        //
        //   ★ `Bytes::BytesLit(Vec<u8>)` replaces `Bytes::StringLit(String)`, so a `"…"` literal
        //     CANNOT be a `Bytes`. Cohort 9 of `rholang_semantic_predicate_ambiguity`
        //     (`[StringLit] CastStr vs CastBytes`) is removed at the DECLARATION.
        //   ★ `lower_arm_cast_bytes` (`rholang-runtime/src/rholang_ast.rs`) lowers to
        //     `new_gbytearray_par` instead of `new_gstring_par`. Under the `String` carrier a
        //     `Bytes` and a `Str` of the same content produced IDENTICAL `Par`s, collapsing
        //     upstream's two distinct wire carriers into one — latent only because `Bytes` was
        //     unreachable in practice, and a genuine consensus defect the moment it was not.
        //
        // URI literals use a bare backtick opener. FLTs remain lexically disjoint because their
        // opener begins with an explicit Rholang selector and result category
        // (`selector:Category\``); a bare backtick can therefore only begin a URI.
        //
        // ⚠ ALSO OUT OF SCOPE HERE, and owed to whoever owns `macros/src/gen/term_ops/`: the
        // `semantic_hash` CATEGORY TAG (#151 thread 2) is still disabled. `2eebf722` measured
        // that with this carrier its five previously-moved goldens pass UNEDITED — they become
        // TRUE rather than re-blessed — so enabling it is now unblocked. Its module comment still
        // enumerates `Bytes::StringLit` among "ALL ELEVEN collection/literal arms"; that name is
        // now `Bytes::BytesLit`.
        ![Vec<u8>] as Bytes
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
        // Closed metasyntax used by Greg/Mike's in-Rholang MeTTaIL DDL.
        // `data` categories have only the constructors declared below: they do
        // not acquire Rholang variables, HOL application/abstraction variants,
        // or object-language auto-injections. This keeps the existing Rholang
        // category/HOL roster and ordinary parser hot path unchanged.
        data DdlImports
        data DdlImport
        data DdlModuleItem
        data DdlParam
        data DdlPath
        data DdlTheoryExpr
        data DdlCatDecl
        data DdlExport
        data DdlReplacement
        data DdlTermRule
        data DdlBinding
        data DdlSort
        data DdlSyntaxItem
        data DdlEquation
        data DdlFreshnesses
        data DdlFreshness
        data DdlRewrite
        data DdlPremises
        data DdlPremise
        data DdlRuleAstItems
        data DdlRuleAstRemainderTail
        data DdlRuleAst

        ![std::sync::Arc<mettail_runtime::ReadZipperLit<Proc, Proc>>] as ReadZipper
        ![std::sync::Arc<mettail_runtime::WriteZipperLit<Proc, Proc>>] as WriteZipper
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
        // ── THE BYTE-ARRAY LITERAL `b"deadbeef"` (ruled 2026-07-29, landed 2026-07-30) ────
        //
        // The `Bytes` category's SURFACE, and the thing whose absence held the `Vec<u8>` carrier
        // back in `2eebf722`. See the `![Vec<u8>] as Bytes` note in `types { … }` above for the
        // full history, the two refuted spellings, and the upstream evidence.
        //
        // ★ HEX, TWO DIGITS PER BYTE — the digits upstream ALREADY PRINTS. Upstream's
        // pretty-printer renders a byte array as bare hex (`pretty_printer.rs:2860`,
        // `GByteArray(bs) => Ok(hex::encode(bs))`) and its own grammar cannot read that back, so
        // upstream prints a value it cannot parse. `b"…"` frames exactly those digits in
        // something the parser accepts: the digits are byte-for-byte upstream's, and the
        // round-trip upstream loses is recovered. That is a BUG FIX, not a divergence — the
        // standing ruling is that upstream is a floor on semantics, not a ceiling on
        // diagnostics. (`par_to_sexpr.rs:107` spells the same value `0x…`; upstream is
        // internally inconsistent here and we rule rather than replicate. `0x…` is refuted
        // twice over: it is already spent on three hex INTEGER forms in this very block, and it
        // is absent from Rholang's grammar entirely.)
        //
        // ★ WHY EVEN-LENGTH IS THE PATTERN AND NOT A CHECK IN `eval`. A byte is two hex digits,
        // so an odd digit count names no byte sequence. Encoding that in the REGEX
        // (`([0-9A-Fa-f][0-9A-Fa-f])*`, pairs) makes the accepted surface language exactly the
        // decodable one, so the `eval` below cannot fail on a token the lexer produced — the
        // failure is impossible rather than handled. `b""` is the empty byte array and is
        // deliberately in the language: it is what `Bytes::BytesLit(vec![])` renders as, and its
        // unrenderability under the empty-delimiter collection arm was the MEASURED blocker.
        //
        // ★ BOTH CASES ACCEPTED, LOWERCASE WRITTEN. `Display` emits lowercase (matching
        // `hex::encode`), so `b"DEADBEEF"` and `b"deadbeef"` are two spellings of one value and
        // canonical idempotence holds after one round. Upstream's `hexToBytes`
        // (`reduce.rs:4849`) is likewise case-insensitive, so accepting both is alignment, not
        // licence.
        //
        // ★ WHY NO EXISTING RHOLANG PROGRAM CHANGES MEANING. Rholang has no juxtaposition, so
        // an identifier immediately followed by a string literal — `b"…"` — is not a term in the
        // language today: it does not parse, so no program contains it. Maximal munch
        // (`LexicographicWeight::open_len`) prefers the 11-byte `b"deadbeef"` token over the
        // 1-byte `Ident("b")`, and AMBIGUITY IS PRESERVED rather than resolved here: the lexer
        // FORKS, the two-token reading stays in the lattice, and it dies on feasibility rather
        // than by decree. A variable named `b` is unaffected in every position where it is not
        // abutted to a `"` — `for (b <- ch) { b }` never reaches this pattern. Pinned by
        // `languages/tests/rholang_byte_literal.rs`.
        Bytes {
            pattern: r#"b"([0-9A-Fa-f][0-9A-Fa-f])*""#;
            eval: ![ {
                // `text` is the whole token INCLUDING the `b"` frame, and the pattern guarantees
                // its shape: a `b`, a `"`, an EVEN number of hex digits, a `"`. Every bound and
                // every digit conversion below is therefore a fact about the token rather than a
                // hope about it.
                //
                // ⚠ NEVER `panic!` here, and never index. This body runs inside the generated
                // parser and, in a consensus setting, on remotely supplied source; a panic
                // cannot be contained in this workspace at all — unwinding across the Cranelift
                // frames of `[profile.dev] codegen-backend = "cranelift"` ABORTS the process
                // rather than failing the parse. Every impossible case answers `Err(())`, which
                // simply DECLINES the reading, so the parser moves on to another lattice branch
                // instead of dying.
                //
                // The decode is a named inner `fn` so that its early exits are `return`s from the
                // DECODER and cannot escape into
                // the surrounding generated closure.
                fn decode_byte_array_literal(text: &str) -> Result<Vec<u8>, ()> {
                    let framed = text.as_bytes();
                    // `b`, `"`, `"` — the shortest word in the language is `b""`, three bytes.
                    if framed.len() < 3 {
                        return Err(());
                    }
                    let digits = &framed[2..framed.len() - 1];
                    if digits.len() % 2 != 0 {
                        return Err(());
                    }
                    // Preallocated at the exact final length: one byte per digit PAIR.
                    let mut decoded: Vec<u8> = Vec::with_capacity(digits.len() / 2);
                    let mut pending_high_nibble: Option<u8> = None;
                    for digit in digits.iter() {
                        let nibble = match digit {
                            b'0'..=b'9' => digit - b'0',
                            b'a'..=b'f' => digit - b'a' + 10,
                            b'A'..=b'F' => digit - b'A' + 10,
                            _ => return Err(()),
                        };
                        match pending_high_nibble {
                            None => pending_high_nibble = Some(nibble),
                            Some(high) => {
                                decoded.push((high << 4) | nibble);
                                pending_high_nibble = None;
                            },
                        }
                    }
                    // Unreachable given the even-length check; answered rather than asserted.
                    match pending_high_nibble {
                        Some(_) => Err(()),
                        None => Ok(decoded),
                    }
                }
                decode_byte_array_literal(text)
            } ]
        }
    },

    // L9-5: Rholang goes MODAL for FLT (foreign-language template) guest bodies.
    // Each `FltOpen*` opener pushes a RAW guest mode whose closer POPs back to
    // the host; the mode stack is a purely LEXICAL balancer resolved before the
    // parser runs (the parser sees an already-bracketed FltOpen…FltClose kind
    // sequence). ZERO-REGRESSION rationale: an opener is the longest maximal-munch
    // accept at its start (its delimiter makes it strictly longer than the bare
    // `Ident`/keyword it collides with — `lam:Proc\`` @9 beats `lam` @3), so under the
    // Delimiter-Unambiguity Invariant the host mode-0 tokenization of every
    // existing Rholang input is byte-identical (no host source contains
    // `IDENT:CAT\`` or the corresponding fence/brace opener). Every form carries
    // an explicit lexical handle reference and qualified result category; no
    // delimiter triggers language inference or an ambient registry lookup.
    tokens {
        // DDL keywords are ordinary grammar literals listed in
        // `contextual_keywords`: their fixed-token reading is available in DDL
        // positions while the Ident co-reading remains available elsewhere.
        // Empty URIs are invalid authority names.  Requiring at least one byte
        // also keeps this token's language disjoint from the doubled suffix of
        // an FLT fence; modal delimiters therefore retain a unique scan.
        UriLiteral = "`[^`]+`" ;

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
        //   * ``lam:Proc`a // b` `` — the FLT guest modes are RAW and declare their own tokens;
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

        FltOpenBacktick = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*(\\.[a-zA-Z_][a-zA-Z0-9_]*)*`" push(flt_body_backtick) ;
        FltOpenFence = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*(\\.[a-zA-Z_][a-zA-Z0-9_]*)*```" push(flt_body_fence) ;
        FltOpenBrace = "[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z_][a-zA-Z0-9_]*(\\.[a-zA-Z_][a-zA-Z0-9_]*)*\\{" push(flt_body_brace) ;

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

        // Official URI-bound names. URI binders form one normalized `New`:
        // f1r3node requires its `New.uri` suffix to be lexicographically sorted,
        // so lowering sorts `(uri,binder)` pairs before extending the de Bruijn
        // environment. Ordinary fresh names can be nested around this form;
        // nesting is the capability-safe normal form because it cannot blur
        // random-name allocation with system-URI authority.
        PNewUris . uris:Vec(Uri), ^[xs].p:[Name* -> Proc]
        |- "new" *zip(uris,xs).*map(|u,x| x "(" u ")").*sep(",") "in" "{" p "}" : Proc;

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
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => match x.checked_bitor(*y) {
                        Some(value) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(value))),
                        None => Proc::Err,
                    },
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
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => match x.checked_bitand(*y) {
                        Some(value) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(value))),
                        None => Proc::Err,
                    },
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
        // `spatial_matcher_pda::ListMachine` (with `sub_pars` supplying
        // connective remainder candidates), and
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
        // semantics is the reducer's own (`spatial_matcher_pda::ListMachine`,
        // with `sub_pars` supplying connective remainder candidates) — again,
        // no second matcher.
        //
        // A self-delimiting parenthesized mixfix in the shape of `int(a, w)`, so
        // it takes a PREFIX binding power (`max_infix_bp + PREFIX_BP_OFFSET`) and
        // consumes no infix precedence slot: it cannot perturb the relative order
        // of any existing operator.
        //
        // `PPar` is contextual, rather than globally reserved. Greg/Mike DDLs use
        // constructor labels such as `PPar` in identifier positions, while this
        // host form uses the same spelling as a leading literal. The generalized
        // parser therefore retains both lexical readings and selects the fixed
        // reading only in this self-delimiting `PPar(φ, ψ)` context. This is the
        // same context-sensitive keyword discipline used by the DDL's own words;
        // it keeps the embedded language's identifier namespace intact without a
        // source rewrite or a second parser.
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: `NaN == NaN` is FALSE. `NaN` is UNORDERED, not equal to itself.
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() == y.get()))),
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: `NaN != NaN` is TRUE — the one NaN predicate that holds.
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() != y.get()))),
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: every ORDERED comparison involving a `NaN` is FALSE.
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() > y.get()))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => crate::rholang::runtime::fixed_ordered_compare(*x, *y, |o| o.is_gt()),
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: every ORDERED comparison involving a `NaN` is FALSE.
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() < y.get()))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => crate::rholang::runtime::fixed_ordered_compare(*x, *y, |o| o.is_lt()),
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: `>=` on an unordered pair is FALSE (it is NOT `!(<)`).
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() >= y.get()))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => crate::rholang::runtime::fixed_ordered_compare(*x, *y, |o| o.is_ge()),
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
                    // ★★ A NUMERIC PREDICATE, so it is IEEE-754 — compared in raw `f64` via
                    // `.get()`, NOT through `CanonicalFloat64`'s `PartialEq`/`Ord`.
                    // IEEE 754 §5.11: `<=` on an unordered pair is FALSE (it is NOT `!(>)`).
                    // The carrier's relations answer a DIFFERENT question and are deliberately
                    // unchanged: `CanonicalFloat64::PartialEq` is reflexive on `NaN` and its `Ord`
                    // sorts `NaN` last, because STRUCTURAL IDENTITY — pattern matching, a `Map`
                    // key, `HashSet` membership, `SemanticHash` — needs an equivalence relation,
                    // and IEEE equality is deliberately irreflexive so it is not one. Two `NaN`
                    // terms therefore remain indistinguishable to matching while `==` answers
                    // `false`; that split is upstream's too (`GDouble` is a `fixed64` of raw bits,
                    // so `Par` equality is bit-comparison, while `combine_relop`'s `GDouble` arm
                    // returns `false` on a `NaN` operand). RULED 2026-07-29.
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x.get() <= y.get()))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => crate::rholang::runtime::fixed_ordered_compare(*x, *y, |o| o.is_le()),
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
        // Every partial numeric arm below uses an explicit checked operation and maps its
        // reported failure onto `Proc::Err`, the `error` term declared above. Fixed-point arms
        // call their checked methods explicitly: raw Rust operators would be safeify-rewritten
        // with `?`, which would decline the entire fold and leave a stuck redex instead of
        // producing Rholang's error term.
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
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => match x.checked_add(*y) {
                        Some(v) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(v))),
                        None => Proc::Err,
                    },
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
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => match x.checked_sub(*y) {
                        Some(v) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(v))),
                        None => Proc::Err,
                    },
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
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => match x.checked_mul(*y) {
                        Some(v) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(v))),
                        None => Proc::Err,
                    },
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
                // ★★ #115, THE ONE TRUE MISSING OPERATOR (declared 2026-07-30).
                //
                // ⚠ THE FILING'S PREMISE WAS REFUTED AND THE DERIVED ANSWER IS A DIFFERENT SET.
                // #115 was filed as "`BigRat` has no binary `-`; `UInt32` has no `-`, `*`, or `/`".
                // Measured over the FULL operator × carrier cross product
                // (`languages/tests/rholang_arith_carrier_matrix.rs`, 78 cells): all four of those
                // cells WORK and preserve their carrier. The cells that did not were
                // `BigRat %`, `Float %`, `Float bitand`, `Float bitor` — and of those four, only
                // `BigRat %` is a gap against the upstream floor:
                //
                //   ▸ `Float %`   — upstream REFUSES IT DELIBERATELY. `combine_mod`'s `GDouble`
                //     arm (`reduce.rs:3425`) is `Err("Modulus not defined on floating point")`, so
                //     the `error` term here already AGREES with upstream. Not a gap; pinned as
                //     floor-conformant rather than "fixed".
                //   ▸ `Float bitand` / `Float bitor` — upstream has NO BITWISE OPERATORS AT ALL
                //     (derived: zero occurrences of `bitand`/`bitor`/`bitnot` anywhere in
                //     `f1r3node-rust-mettail`, and none in the consensus tree-sitter grammar), so
                //     there is no floor to meet and the disposition is ours to rule. RULED: they
                //     stay the `error` term. A bitwise operation on an IEEE-754 float has no
                //     arithmetic meaning — the only implementable reading is masking the bit
                //     PATTERN, which is not a function of the represented VALUE (`-0.0` and `0.0`
                //     are equal floats with different patterns), so it would break the one
                //     property every other arm here has: that the answer depends only on the
                //     operands' values. Failing closed is the correct answer, not a missing one.
                //
                // `BigRat %` IS a gap: upstream's `combine_mod` `GBigRat` arm
                // (`reduce.rs:3435-3444`) answers the RATIONAL ZERO for any non-zero divisor, and
                // `Modulo by zero` when the divisor's numerator is zero. That is not an
                // approximation — in the FIELD ℚ every non-zero `b` divides every `a` exactly
                // (`a = (a/b)·b` with `a/b ∈ ℚ`), so the remainder is identically 0. This arm
                // reproduces it exactly, including the divide-by-zero refusal.
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(_), BigRat::RatLit(y)) => {
                        // `y.get()` is the `Ratio<BigInt>`; `is_zero` is `num_traits::Zero`, the
                        // same route `BigInt`'s arm above uses. A rational is zero exactly when its
                        // numerator is, which is also upstream's test (`is_zero_twos_complement`
                        // on `r2.numerator`).
                        if y.get().is_zero() {
                            Proc::Err
                        } else {
                            // The rational ZERO, built through the canonicalizing constructor so
                            // the payload is the same interned value `0r` parses to. `try_from_nd`
                            // is fallible only for a zero DENOMINATOR, which `1` is not; the
                            // impossible branch is answered rather than asserted, because a
                            // `panic!` in a fold body aborts the process under the cranelift dev
                            // backend.
                            match mettail_runtime::CanonicalBigRat::try_from_nd(
                                num_bigint::BigInt::from(0),
                                num_bigint::BigInt::from(1),
                            ) {
                                Some(zero) => {
                                    Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(zero)))
                                },
                                None => Proc::Err,
                            }
                        }
                    }
                    _ => Proc::Err,
                },
                // Upstream's fixed-point remainder is `u_a % u_b` on equal-scale mantissas,
                // preserving that scale. `checked_rem` also rejects a zero divisor and refuses
                // mismatched scales, so this arm matches both upstream's value and its accepted
                // operand domain.
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

        // Rholang constructors and the receiver-first method surface.
        //
        // `Map()` is an alias for the empty brace literal `{}`.
        // Method calls have one grammar constructor below; their semantics are
        // exclusively owned by the reducer.
        MapEmpty .
        |- "Map" "(" ")" : Proc ![{
            Proc::CastMap(std::sync::Arc::new(Map::MapLit(
                mettail_runtime::HashMapLit::<Proc, Proc>::new(),
            )))
        }] fold;

        PathmapEmpty .
        |- "Pathmap" "(" ")" : Proc ![{
            Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(
                mettail_runtime::PathMapLit::<Proc, Proc>::new(),
            )))
        }] fold;

        // A method call is syntax, not a second method registry or a host evaluator.
        //
        // The former surface declared 47 name-specific rules, which made every method
        // name a global lexer terminal and duplicated the reducer's independently
        // evolving method table. Capturing the name as the builtin Ident token keeps the
        // parser neutral: every syntactically valid method name has one AST shape, the
        // exact name and ordered arguments round-trip as data, and the reducer decides
        // membership, arity, carrier support, cost, and result.
        //
        // No fold body is deliberate. Evaluating either the receiver or an argument in
        // Dovetail would recreate the host/machine semantic fork this node removes.
        // MethodCallReceiverWithheld below severs the scalar receiver position. The
        // Vec(Proc) argument field already lowers as one labelled, invertible FieldSeqProc
        // leaf, so its members are not child e-classes and cannot be rewritten there.
        MethodCall . receiver:Proc, method_name:Ident, arguments:Vec(Proc)
        |- receiver "." method_name "(" arguments.*sep(",") ")" : Proc;

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

        // Keep newly introduced categories additive to the legacy generated
        // parser ABI. Category indices are derived from the term dependency
        // order, so placing UriText before PZero would renumber Proc,
        // InputBind, ForRow, and Name even though URI syntax does not alter
        // their grammar. Token-text capture preserves the complete framed URI
        // without routing its bytes through the string-literal family or an
        // FLT mode.
        UriText . |- raw@UriLiteral : Uri;

        // L9-5: FLT guest-body captures. Each `*flt(node, open, close)` consumes a
        // delimited foreign-language region and assembles an opaque native
        // `FltNode` containing the lexical selector, explicit result category,
        // ordered ranged Text/Hole pieces, stable telescope, and checked finite
        // extent (an inert BoundTerm leaf). The three forms differ ONLY in surface
        // delimiter; all carry the same `Arc<FltNode>` payload. Guest parsing is
        // staged until the selector resolves to an installed handle, so no `eval`
        // disposition is declared. Declared LAST so the
        // existing Proc rule indices (and the pinned @/mixfix cohort structure)
        // are unperturbed — a leading-capture rule joins no infix/mixfix cohort.
        PFlt . |- *flt(node, FltOpenBacktick, FltCloseBacktick) : Proc;
        PFltFence . |- *flt(node, FltOpenFence, FltCloseFence) : Proc;
        PFltBrace . |- *flt(node, FltOpenBrace, FltCloseBrace) : Proc;

        // Greg/Mike MeTTaIL DDL declarations are first-class forms of this
        // existing Rholang Proc. Every field below is parsed structurally by
        // this generated parser. No declaration source is captured or parsed a
        // second time.

        // Theory algebra, loosest to tightest. Postfix builders are classified
        // separately and bind tighter than these left-associative infixes.
        DdlTheoryDiff . left:DdlTheoryExpr, right:DdlTheoryExpr
            |- left "\\" right : DdlTheoryExpr;
        DdlTheoryJoin . left:DdlTheoryExpr, right:DdlTheoryExpr
            |- left "\\/" right : DdlTheoryExpr;
        DdlTheoryMeet . left:DdlTheoryExpr, right:DdlTheoryExpr
            |- left "/\\" right : DdlTheoryExpr;

        DdlTheoryTypes . base:DdlTheoryExpr, entries:Vec(DdlCatDecl)
            |- base "Types" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryExports . base:DdlTheoryExpr, entries:Vec(DdlExport)
            |- base "Exports" "{" entries.*sep("") "}" : DdlTheoryExpr same;
        DdlTheoryReplacements . base:DdlTheoryExpr, entries:Vec(DdlReplacement)
            |- base "Replacements" "{" entries.*sep("") "}" : DdlTheoryExpr same;
        DdlTheoryTerms . base:DdlTheoryExpr, entries:Vec(DdlTermRule)
            |- base "Terms" "{" entries.*sep("") "}" : DdlTheoryExpr same;
        DdlTheoryEquations . base:DdlTheoryExpr, entries:Vec(DdlEquation)
            |- base "Equations" "{" entries.*sep("") "}" : DdlTheoryExpr same;
        DdlTheoryRewrites . base:DdlTheoryExpr, entries:Vec(DdlRewrite)
            |- base "Rewrites" "{" entries.*sep("") "}" : DdlTheoryExpr same;
        DdlTheoryData . base:DdlTheoryExpr, value:Proc
            |- base "Data" "(" value ")" : DdlTheoryExpr same;

        DdlTheoryEmpty . |- "Empty" : DdlTheoryExpr;
        DdlTheoryFree . path:DdlPath
            |- "free" "(" path ")" : DdlTheoryExpr;
        DdlTheoryLet . bound:DdlTheoryExpr, body:DdlTheoryExpr
            |- "let" name@Ident "=" bound "in" "(" body ")" : DdlTheoryExpr;
        DdlTheoryBraceGroup . body:DdlTheoryExpr |- "{" body "}" : DdlTheoryExpr;
        DdlTheoryParenGroup . body:DdlTheoryExpr |- "(" body ")" : DdlTheoryExpr;
        DdlTheoryApply . path:DdlPath, arguments:Vec(DdlTheoryExpr)
            |- path "(" arguments.*sep(",") ")" : DdlTheoryExpr;
        DdlTheoryRef . path:DdlPath |- path : DdlTheoryExpr;

        // G5: a leading builder has an implicit Empty base.
        DdlTheoryTypesImplicit . entries:Vec(DdlCatDecl)
            |- "Types" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryExportsImplicit . entries:Vec(DdlExport)
            |- "Exports" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryReplacementsImplicit . entries:Vec(DdlReplacement)
            |- "Replacements" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryTermsImplicit . entries:Vec(DdlTermRule)
            |- "Terms" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryEquationsImplicit . entries:Vec(DdlEquation)
            |- "Equations" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryRewritesImplicit . entries:Vec(DdlRewrite)
            |- "Rewrites" "{" entries.*sep("") "}" : DdlTheoryExpr;
        DdlTheoryDataImplicit . value:Proc
            |- "Data" "(" value ")" : DdlTheoryExpr;

        DdlPathQualified . tail:DdlPath |- head@Ident "." tail : DdlPath;
        DdlPathName . |- name@Ident : DdlPath;
        DdlParamDecl . theory:DdlPath |- name@Ident ":" theory : DdlParam;

        DdlImportModuleAs .
            |- "import" raw@StringLiteral "as" alias@Ident : DdlImport;
        DdlImportFromModule .
            |- "import" name@Ident "from" raw@StringLiteral : DdlImport;
        DdlImportsNonEmpty . head:DdlImport, tail:Vec(DdlImport)
            |- head tail.*sep("") : DdlImports;

        // BNFC's `ProgTheoryInst ::= "theory" TheoryInst` consumes the complete
        // `TheoryInst` entrypoint. This is not a tight unary operator. The zero
        // Pratt floor is the exact translation: it admits the constructor and
        // theory-algebra continuations belonging to the selected expression.
        DdlModuleTheoryItem . expression:DdlTheoryExpr
            |- "theory" expression : DdlModuleItem prefix(0);
        DdlModuleProcItem . process:Proc |- process : DdlModuleItem;

        DdlModule . items:Vec(DdlModuleItem)
            |- "Module" name@Ident "{" items.*sep("") "}" : Proc;
        DdlModuleImported . imports:DdlImports, items:Vec(DdlModuleItem)
            |- imports "Module" name@Ident "{" items.*sep("") "}" : Proc;
        DdlTheory . parameters:Vec(DdlParam), body:DdlTheoryExpr
            |- "Theory" name@Ident "(" parameters.*sep(",") ")" "{" body "}" : Proc;

        DdlCategory . |- name@Ident ";" : DdlCatDecl;
        DdlExportDirect . |- name@Ident ";" : DdlExport;
        DdlExportRename .
            |- name@Ident "=>" replacement@Ident ";" : DdlExport;
        DdlReplacementRule . rule:DdlTermRule
            |- target@Ident "=>" rule : DdlReplacement;

        DdlTerm . bindings:Vec(DdlBinding), syntax:Vec(DdlSyntaxItem)
            |- label@Ident "." bindings.*sep(",") "|-" syntax.*sep("") ":" result@Ident ";" : DdlTermRule;
        DdlBindingPlain . sort:DdlSort |- name@Ident ":" sort : DdlBinding;
        DdlBindingBinder .
            |- "^" binder@Ident "." body@Ident ":" "[" from@Ident "->" to@Ident "]" : DdlBinding;

        DdlSortHashBag . |- "HashBag" "(" of@Ident ")" : DdlSort;
        DdlSortSet . |- "Set" "(" of@Ident ")" : DdlSort;
        DdlSortList . |- "List" "(" of@Ident ")" : DdlSort;
        DdlSortCategory . |- name@Ident : DdlSort;

        DdlSyntaxProjection .
            |- argument@Ident "." "*" "sep" "(" raw@StringLiteral ")" : DdlSyntaxItem;
        DdlSyntaxTerminal . |- raw@StringLiteral : DdlSyntaxItem;
        DdlSyntaxArgument . |- argument@Ident : DdlSyntaxItem;

        DdlFreshness .
            |- "if" left@Ident "#" right@Ident "then" : DdlFreshness;
        DdlFreshnessOne . condition:DdlFreshness |- condition : DdlFreshnesses;
        DdlFreshnessMore . condition:DdlFreshness, rest:DdlFreshnesses
            |- condition rest : DdlFreshnesses;
        DdlEquationDirect . left:DdlRuleAst, right:DdlRuleAst
            |- left "==" right ";" : DdlEquation;
        DdlEquationConditional . freshness:DdlFreshnesses, left:DdlRuleAst, right:DdlRuleAst
            |- freshness left "==" right ";" : DdlEquation;

        DdlPremise .
            |- "if" left@Ident "~>" right@Ident "then" : DdlPremise;
        DdlPremiseOne . premise:DdlPremise |- premise : DdlPremises;
        DdlPremiseMore . premise:DdlPremise, rest:DdlPremises |- premise rest : DdlPremises;
        DdlRewriteDirect . left:DdlRuleAst, right:DdlRuleAst
            |- name@Ident ":" left "~>" right ";" : DdlRewrite;
        DdlRewriteConditional . premises:DdlPremises, left:DdlRuleAst, right:DdlRuleAst
            |- name@Ident ":" premises left "~>" right ";" : DdlRewrite;

        DdlRuleAstSubst . abstraction:DdlRuleAst, argument:DdlRuleAst
            |- "(" "subst" abstraction argument ")" : DdlRuleAst;
        DdlRuleAstSExp . arguments:Vec(DdlRuleAst)
            |- "(" label@Ident arguments.*sep("") ")" : DdlRuleAst;
        DdlRuleAstAbs . body:DdlRuleAst |- "^" binder@Ident "." body : DdlRuleAst;
        DdlRuleAstCollectionEmpty . |- "{" "}" : DdlRuleAst;
        DdlRuleAstCollection . items:DdlRuleAstItems |- "{" items "}" : DdlRuleAst;
        DdlRuleAstRemainderOnly . |- "{" "..." remainder@Ident "}" : DdlRuleAst;
        DdlRuleAstCollectionRemainder . first:DdlRuleAst, tail:DdlRuleAstRemainderTail
            |- "{" first "," tail "}" : DdlRuleAst;
        DdlRuleAstVar . |- name@Ident : DdlRuleAst;
        DdlRuleAstItemOne . item:DdlRuleAst |- item : DdlRuleAstItems;
        DdlRuleAstItemMore . item:DdlRuleAst, rest:DdlRuleAstItems
            |- item "," rest : DdlRuleAstItems;
        DdlRuleAstTailRemainder . |- "..." remainder@Ident : DdlRuleAstRemainderTail;
        DdlRuleAstTailMore . item:DdlRuleAst, rest:DdlRuleAstRemainderTail
            |- item "," rest : DdlRuleAstRemainderTail;

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

        // Method execution belongs to the reducer, including evaluation of the
        // receiver and every ordered argument. Dovetail therefore treats the
        // receiver as payload rather than an e-class child. The argument Vec is
        // already a single FieldSeqProc leaf; declaring a nested per-element
        // withholding would be both redundant and correctly refused by the
        // withholding classifier.
        MethodCallReceiverWithheld . | S ~/> T
        |- (MethodCall S M Args) ~> (MethodCall T M Args);

        CastMapCong . | S ~> T |- (CastMap S) ~> (CastMap T);
        CastSetCong . | S ~> T |- (CastSet S) ~> (CastSet T);
        CastPathmapCong . | S ~> T |- (CastPathmap S) ~> (CastPathmap T);
        CastReadZipperCong . | S ~> T |- (CastReadZipper S) ~> (CastReadZipper T);
        CastWriteZipperCong . | S ~> T |- (CastWriteZipper S) ~> (CastWriteZipper T);
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
