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
/// (`rholang-runtime::rhocalc_formula`). `pub`, not `pub(crate)`, precisely so
/// there is ONE classification and the two consumers cannot drift apart.
pub mod formula;
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
    name: RhoCalc,

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
        ![std::sync::Arc<crate::rhocalc::zipper::ReadZipperLit>] as ReadZipper
        ![std::sync::Arc<crate::rhocalc::zipper::WriteZipperLit>] as WriteZipper
    },

    // ── Divergence I (2026-07-25): the integer-literal DOMAINS PARTITION ────────────
    //
    // f1r3node's `normalize_ground` (`ground_normalize_matcher.rs:14-50`) is a TOTAL
    // function from a Rholang numeral to exactly ONE ground carrier:
    //
    //     bare digits ▸ GInt        `…i32` / `…i64` ▸ GInt
    //     `…u32` (≤ i64::MAX) ▸ GInt        `…n` ▸ GBigInt
    //
    // so **`Int` is THE ≤64-bit literal carrier** and **`UInt32` has NO literal
    // surface** — the 32-bit wraparound carrier is reachable ONLY through the
    // MeTTaIL-only `uint(x, 32)` cast. Each `eval` below therefore accepts EXACTLY
    // the spellings its own `pattern` declares, and the three accepted domains are
    // pairwise DISJOINT, so a numeral's carrier is a function of the numeral TEXT
    // and of nothing else — no election, no context, no parentheses.
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
    literals {
        Int {
            // The full `normalize_ground` ≤64-bit suffix set. `(i64)?` alone left
            // `5i32`/`5u32` un-lexable as a single `Int` token even though both are
            // `GInt` upstream.
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i32|i64|u32)?";
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
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r";
            eval: ![ {
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

    // L9-5: RhoCalc goes MODAL for FLT (foreign-language template) guest bodies.
    // Each `FltOpen*` opener pushes a RAW guest mode whose closer POPs back to
    // the host; the mode stack is a purely LEXICAL balancer resolved before the
    // parser runs (the parser sees an already-bracketed FltOpen…FltClose kind
    // sequence). ZERO-REGRESSION rationale: an opener is the longest maximal-munch
    // accept at its start (its delimiter makes it strictly longer than the bare
    // `Ident`/keyword it collides with — `lam\`` @4 beats `lam` @3), so under the
    // Delimiter-Unambiguity Invariant the host mode-0 tokenization of every
    // existing RhoCalc input is byte-identical (no host source contains
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
        // `hidden_tokens_to_left/right`. It is NOT observable by a running RhoCalc program:
        // only `DEFAULT` feeds the parser and the program.
        //
        // This REPLACES the `rhocalc` binary's pre-parse `strip_comments` preprocessor, which
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

    terms {
        PZero .
        |- "Nil" : Proc;

        PDrop . n:Name  |- "*" n : Proc ;

        // AST-level constructor for parallel composition (multiset of procs).
        // Equations / rewrites match on `(PPar {…})`. User-facing surface
        // syntax is either braced `{ P | Q }` or bare infix `P | Q` (`PParInfix`,
        // folded via `merge_pp_parallel`). The `__ppar(…)` keyword exposes the
        // constructor for internal use and round-trip parsing of normalized AST.
        //
        // Top-level `{ … }` is also used for Map literals (`{ k: v }`); the
        // parser disambiguates on `:` vs `|`. Empty `{}` is an empty Map.
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
        PParInternal . ps:HashBag(Proc) |- "__ppar" "(" ps.*sep(",") ")" : Proc ![{
            Proc::PPar(ps.clone())
        }] fold;

        POutput . n:Name, q:Proc
        |- n "!" "(" q ")" : Proc ;
        PPersistOutput . n:Name, q:Proc
        |- n "!!" "(" q ")" : Proc ;
        // Empty send sugar: `x!()` parses as `x!([])`.
        POutputEmpty . n:Name
        |- n "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        // Empty persistent send sugar: `x!!()` parses as `x!!([])`.
        PPersistOutputEmpty . n:Name
        |- n "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(n.clone()),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
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
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
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
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
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
            Proc::POutput(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rhocalc::receive::name_pattern_to_proc(&n)))), std::sync::Arc::new(q.clone()))
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
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        PPersistOutputNilEmpty .
        |- "@" "Nil" "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        POutputQuotedEmpty . n:Name
        |- "@" n "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rhocalc::receive::name_pattern_to_proc(&n)))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
            )
        }] fold;
        POutputShortEmpty . p:Proc
        |- "@" p "!" "(" ")" : Proc ![{
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
            )
        }] fold prefix(220);
        PPersistOutputShortEmpty . p:Proc
        |- "@" p "!!" "(" ")" : Proc ![{
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(vec![])),
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
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
            )
        }] fold;
        PPersistOutputNil2Plus . a:Proc, bs:Vec(Proc)
        |- "@" "Nil" "!!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
            )
        }] fold;
        POutputQuoted2Plus . n:Name, a:Proc, bs:Vec(Proc)
        |- "@" n "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(crate::rhocalc::receive::name_pattern_to_proc(&n)))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
            )
        }] fold;
        POutputShort2Plus . p:Proc, a:Proc, bs:Vec(Proc)
        |- "@" p "!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::POutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
            )
        }] fold prefix(220);
        PPersistOutputShort2Plus . p:Proc, a:Proc, bs:Vec(Proc)
        |- "@" p "!!" "(" a "," bs.*sep(",") ")" : Proc ![{
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.clone());
            items.extend(bs.clone());
            Proc::PPersistOutput(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
            )
        }] fold prefix(220);

        // Internal guard gate used by where-clause gating.
        GuardThen . cond:Proc, body:Proc
        |- "__guard_then" "(" cond "," body ")" : Proc ![{
            crate::rhocalc::receive::guard_then(&cond, &body)
        }] fold;

        // Internal helper for where-guarded communication.
        // Produces reduced body when match+guard succeed; otherwise returns the original
        // receive/send pair unchanged (blocked communication, identity).
        CommWhere . pat:Proc, n:Name, q:Proc, cond:Proc, body:Proc
        |- "__comm_where" "(" pat "<-" n "," q "," cond "," body ")" : Proc ![{
            crate::rhocalc::receive::comm_pforwhere_subst(&pat, &n, &q, &cond, &body)
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
            items.push(crate::rhocalc::receive::name_pattern_to_proc(&lhs));
            items.extend(lhss.iter().map(crate::rhocalc::receive::name_pattern_to_proc));
            InputBind::InputBindQuoted(
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
                std::sync::Arc::new(n.clone()),
            )
        }] fold;
        InputBindPersistentPolyadic . lhs:Name, lhss:Vec(Name), n:Name
        |- lhs "," lhss.*sep(",") "<=" n : InputBind ![{
            let mut items = Vec::with_capacity(1 + lhss.len());
            items.push(crate::rhocalc::receive::name_pattern_to_proc(&lhs));
            items.extend(lhss.iter().map(crate::rhocalc::receive::name_pattern_to_proc));
            InputBind::InputBindQuotedPersistent(
                std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
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
        // (receive.rs `try_comm_on_pfor_user` / rhocalc_ast.rs
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
            crate::rhocalc::receive::desugar_for_rows(rows, body)
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
        NQuoteShort . p:Proc
        |- "@" p : Name ![{
            Name::NQuote(std::sync::Arc::new(p.clone()))
        }] fold prefix(220);

        // Parenthesized Name grouping used by `*(x)` compatibility.
        NParen . n:Name
        |- "(" n ")" : Name ![{ n.clone() }] fold;

        // `new` — OFFICIAL RHOLANG SURFACE (tree-sitter `grammar.js:89-93`,
        // BNFC `rholang_mercury.cf:72`):
        //
        //     new:        prec(1, seq('new', $.name_decls, 'in', $._proc))
        //     name_decls: commaSep1($.name_decl)
        //     PNew.       Proc1 ::= "new" [NameDecl] "in" Proc1 ;
        //
        // RhoCalc IS Rholang, so the declaration list carries NO GROUPING
        // PARENTHESES: `new x, y in { P }`. The pre-2026-07-24 RhoCalc-only
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
        // `languages/tests/rhocalc_new_official_syntax.rs`.
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
        // `NegProc` is declared after `/` and `%` so `-` binds tighter than division (e.g. `-3r/2r` is `(-3r)/2r`).
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
            crate::rhocalc::runtime::merge_pp_parallel(a.clone(), b.clone())
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
        // Boolean algebra RhoCalc's `bool` inhabits, which is exactly where the Heyting `⇒`
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::unary_fallback(a, || {
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
        // contributes the pattern COMPILER (`rholang-runtime/src/rhocalc_formula.rs`),
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
        // the same relative order official Rholang gives. (RhoCalc assigns ONE
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
        Matches . a:Proc, p:Proc |- a "matches" p : Proc ;

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
        // ⚠ `"PPar"` becomes a RESERVED word. RhoCalc sets
        // `options { reserved_keywords: auto }` (above), which reserves every
        // identifier-shaped literal terminal, so after this declaration `PPar` can
        // no longer name a variable. That is the whole point — reservation is what
        // makes the leading literal unable to fork against the lowercase call-forms
        // (`int(…)`, `bool(…)`, a user method) — and it is affordable because the
        // name is unused: no `.rho` demo, corpus program, or RhoCalc test binds
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
                // RhoCalc conforms DOWN to Rholang.
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                _ => {
                    // Cross-kind comparison. An operand that is still a REDEX rebuilds the `==`
                    // so congruence reduces it first; `error` is reserved for two ground operands
                    // the collection comparator cannot decide (see `runtime::is_ground_operand`
                    // — without this, `*(@(1)) == 1` answers `error`).
                    if !crate::rhocalc::runtime::both_ground(a, b) {
                        Proc::Eq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                    } else if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(&a, &b) {
                        Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(v)))
                    } else {
                        Proc::Err
                    }
                },
            }}
        ] fold;

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
                    if !crate::rhocalc::runtime::both_ground(a, b) {
                        Proc::Ne(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                    } else if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(&a, &b) {
                        Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!v)))
                    } else {
                        Proc::Err
                    }
                },
            }}
        ] fold;

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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::Lt(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::GtEq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::LtEq(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

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
        // have always used for ÷0. Pinned by `rholang-runtime/tests/rho_rhocalc_conformance.rs`
        // (divergences A / A2).
        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_add(*x, *y) {
                            Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            None => Proc::Err,
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
                            Some(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            None => Proc::Err,
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
                        match <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_add(*x, *y) {
                            Some(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            None => Proc::Err,
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::Add(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_sub(*x, *y) {
                            Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                // `u32` subtraction underflows (and panics) whenever `x < y`; checked here.
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        match <u32 as mettail_runtime::SafeArith>::safe_sub(*x, *y) {
                            Some(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            None => Proc::Err,
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
                        match <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_sub(*x, *y) {
                            Some(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            None => Proc::Err,
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::Sub(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_mul(*x, *y) {
                            Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        match <u32 as mettail_runtime::SafeArith>::safe_mul(*x, *y) {
                            Some(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(v))),
                            None => Proc::Err,
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
                        match <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_mul(*x, *y) {
                            Some(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                            None => Proc::Err,
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
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
                            Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            None => Proc::Err,
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
                    // Division by zero is an error (consistent with the integer/rational/fixed
                    // arms); `safe_div` alone would answer `±Inf` for `x / 0.0` (it preserves
                    // infinities and rejects only NaN), so the explicit zero guard stays.
                    (Float::FloatLit(x), Float::FloatLit(y)) => {
                        if y.get() == 0.0 {
                            Proc::Err
                        } else {
                            match <mettail_runtime::CanonicalFloat64 as mettail_runtime::SafeArith>::safe_div(*x, *y) {
                                Some(v) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(v))),
                                None => Proc::Err,
                            }
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::Div(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        Mod . a:Proc, b:Proc |- a "%" b : Proc ![
            { match (&a, &b) {
                // `safe_rem` is `i64::checked_rem`: `None` for `y == 0` and for `i64::MIN % -1`.
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => {
                        match <i64 as mettail_runtime::SafeArith>::safe_rem(*x, *y) {
                            Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                            None => Proc::Err,
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
                _ => crate::rhocalc::runtime::binary_fallback(a, b, || {
                    Proc::Mod(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))
                }),
            }}
        ] fold;

        NegProc . a:Proc |- "-" a : Proc ![
            { match &a {
                // `-i64::MIN` overflows (and panics); `safe_neg` is `checked_neg`.
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(n) => match <i64 as mettail_runtime::SafeArith>::safe_neg(*n) {
                        Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v))),
                        None => Proc::Err,
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
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(-f.get())))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(fp.clone().neg()))),
                    _ => Proc::Err,
                },
                // See `runtime::is_ground_operand`: `error` only for a ground operand.
                _ => crate::rhocalc::runtime::unary_fallback(a, || {
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
            Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(
                mettail_runtime::PathMapLit::<Proc, Proc>::new(),
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
                        match crate::rhocalc::pathmap::pathmap_get(payload, &k) {
                            Ok(Some(v)) => v,
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
                        match crate::rhocalc::pathmap::pathmap_put(payload, &k, &v) {
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
                        payload.contains(&crate::rhocalc::runtime::normalize_collection_element(&k)),
                    ))),
                    _ => Proc::Err,
                },
                Proc::CastPathmap(inner) => match inner.as_ref() {
                    Pathmap::PathmapLit(ref payload) => {
                        match crate::rhocalc::pathmap::pathmap_has(payload, &k) {
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
                        new_set.remove(&crate::rhocalc::runtime::normalize_collection_element(&k));
                        Proc::CastSet(std::sync::Arc::new(Set::SetLit(new_set)))
                    },
                    _ => Proc::Err,
                },
                Proc::CastList(l) => match (l.as_ref(), &k) {
                    (List::ListLit(v), Proc::CastInt(ii)) => match &**ii {
                        Int::NumLit(n) => {
                            let idx = *n as usize;
                            let mut vec = v.clone();
                            if idx >= vec.len() {
                                panic!("delete: index out of bounds");
                            }
                            vec.remove(idx);
                            crate::rhocalc::runtime::mk_proc_list(vec)
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
                        match crate::rhocalc::pathmap::pathmap_merge(pa, pb) {
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
        // (`rholang-runtime/src/rhocalc_ast.rs::lower_method`).
        //
        // It previously folded host-side through a hand-maintained FORK of f1r3node's `rhoapi`
        // protobuf schema (`languages/proto/rhocalc_wire.proto` + `languages/src/rhocalc/wire.rs`),
        // which was retired because it encoded a DIFFERENT Rholang term than RhoCalc means:
        // its 7-message schema had no `g_big_int` field, while a plain RhoCalc integer literal is
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
                    Map::MapLit(ref payload) => crate::rhocalc::runtime::mk_proc_set(
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
                    Map::MapLit(ref payload) => crate::rhocalc::runtime::mk_proc_list(
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
            crate::rhocalc::runtime::fold_proc_length(&l)
        }] fold;

        // `l.nth(i)` — Rholang's `nth` (`reduce.rs::method_table`), which is TOTAL on the
        // carrier: it is defined for every index the language can write, and an out-of-range
        // index is a recoverable failure, never a crash.
        //
        // Divergence **C**, closed 2026-07-25 (was pinned by
        // `rholang-runtime/tests/rho_rhocalc_conformance.rs`):
        //
        //   1. the index arm accepted only `Proc::CastInt` (a fixed-width `int(i, w)`), so the
        //      DEFAULT RhoCalc integer literal — which is arbitrary-precision `BigInt` — was
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

        LConcat . l:Proc, r:Proc
        |- l "." "concat" "(" r ")" : Proc ![{
            match (&l, &r) {
                (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
                    (List::ListLit(va), List::ListLit(vb)) => {
                        let mut o = va.clone();
                        o.extend(vb.iter().cloned());
                        crate::rhocalc::runtime::mk_proc_list(o)
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

        // ── rhocalc Bag methods ──────────────────────────────────────────
        BCount . b:Proc, e:Proc
        |- b "." "count" "(" e ")" : Proc ![{
            match &b {
                Proc::CastBag(bag) => match bag.as_ref() {
                    Bag::BagLit(h) => {
                        let normalized = crate::rhocalc::runtime::normalize_bag_elements(h);
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
                        let normalized = crate::rhocalc::runtime::normalize_bag_elements(h);
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
                        match crate::rhocalc::pathmap::pathmap_restrict(pa, pb) {
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
                        match crate::rhocalc::pathmap::pathmap_subtract(pa, pb) {
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
                        match crate::rhocalc::pathmap::pathmap_meet(pa, pb) {
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
                        match crate::rhocalc::zipper::path_get_subtrie(lit) {
                            Ok(out) => Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(out))),
                            Err(()) => Proc::Err,
                        }
                    },
                    _ => Proc::Err,
                },
                Proc::CastReadZipper(inner) => match inner.as_ref() {
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_get_subtrie(z.as_ref()) {
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
                        match crate::rhocalc::zipper::path_get_subtrie_at(lit, path) {
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
                        match crate::rhocalc::zipper::read_zipper_root(lit) {
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
                        match crate::rhocalc::zipper::read_zipper_at(lit, path) {
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
                        match crate::rhocalc::zipper::write_zipper_root(lit) {
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
                        match crate::rhocalc::zipper::write_zipper_at(lit, path) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_get_leaf(z.as_ref()) {
                        Ok(v) => v,
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_descend_to(z.as_ref(), rel) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_child_count(z.as_ref()) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_descend_first(z.as_ref()) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_to_next_sibling(z.as_ref()) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_to_prev_sibling(z.as_ref()) {
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
            // The branch index `i` is a rhocalc integer literal, which lexes to
            // `BigInt` (see RZAscend). Accept both `CastBigInt` and `CastInt` via
            // `proc_to_index` so the merged grammar reduces (this op was
            // merge-added from `main`, where the literal would have been
            // `CastInt`).
            match (&z, crate::rhocalc::zipper::proc_to_index(&i)) {
                (Proc::CastReadZipper(inner), Some(n)) => match inner.as_ref() {
                    ReadZipper::Lit(z) => {
                        match crate::rhocalc::zipper::zipper_descend_indexed_branch(z.as_ref(), n) {
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
                    ReadZipper::Lit(z) => match crate::rhocalc::zipper::zipper_ascend_one(z.as_ref()) {
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
            // The step count `n` is a rhocalc integer literal. Bare integers in
            // rhocalc lex to `BigInt` (Rholang 1.4 arbitrary-precision default),
            // so `n` arrives as `Proc::CastBigInt(NumLit)` — NOT `Proc::CastInt`.
            // This op was merge-added from `main`, whose integer literals were
            // `CastInt`; `proc_to_index` accepts BOTH forms so the merged grammar
            // reduces instead of falling through to `Proc::Err`.
            match (&z, crate::rhocalc::zipper::proc_to_index(&n)) {
                (Proc::CastReadZipper(inner), Some(steps)) => match inner.as_ref() {
                    ReadZipper::Lit(z) => {
                        match crate::rhocalc::zipper::zipper_ascend(z.as_ref(), steps) {
                            Ok(out) => Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(out)))),
                            Err(()) => Proc::Err,
                        }
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
                        match crate::rhocalc::zipper::write_zipper_set_leaf(z.as_ref(), fp, val) {
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
                        match crate::rhocalc::zipper::write_zipper_set_subtrie(z.as_ref(), rel_lit) {
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
                    WriteZipper::Lit(z) => match crate::rhocalc::zipper::write_zipper_remove_leaf(z.as_ref()) {
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
                        match crate::rhocalc::zipper::write_zipper_remove_branches(z.as_ref()) {
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
                        match crate::rhocalc::zipper::write_zipper_graft(z.as_ref(), src.as_ref()) {
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
                        match crate::rhocalc::zipper::write_zipper_join_into(z.as_ref(), src.as_ref()) {
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
                        new_set.insert(crate::rhocalc::runtime::normalize_collection_element(&e));
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
                _ => crate::rhocalc::runtime::unary_fallback(a, || {
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
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(s.parse::<bool>().unwrap_or(false)))),
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
                    std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
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
                    std::sync::Arc::new(crate::rhocalc::runtime::mk_proc_list(items)),
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
            let res = crate::rhocalc::runtime::merge_pp_parallel(a.as_ref().clone(), b.as_ref().clone());

        // Evaluate guarded communication helper introduced by CommPatternWhere.
        // This bridges rewrite-time construction (`CommWhere ...`) to runtime semantics:
        // - successful match + true guard => reduced body
        // - mismatch / false guard => original receive+send pair (identity)
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::CommWhere(ref pat, ref n, ref q, ref cond, ref body) = s,
            let res = crate::rhocalc::receive::comm_pforwhere_subst(
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
            if crate::rhocalc::receive::pfor_user_still_has_query_rows(rows),
            let res = crate::rhocalc::receive::desugar_for_rows(rows.clone(), body.as_ref());

        // `PForUser` communication (replaces declarative Comm* rewrites on `PFor` / `PForWhere` / `PForJoin`).
        rw_proc(s0.clone(), res) <--
            eq_proc(s0, s),
            if let Some(rewritten) = crate::rhocalc::receive::try_comm_rw_proc(&s),
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
