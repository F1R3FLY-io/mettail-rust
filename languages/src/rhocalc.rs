#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use num_traits::Zero;
use std::ops::Neg;

pub(crate) mod pathmap;
pub(crate) mod receive;
pub(crate) mod runtime;
mod type_inference;
pub(crate) mod wire;
pub(crate) mod zipper;

language! {
    name: RhoCalc,

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

    literals {
        UInt32 {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)u32";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
        Int {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i64)?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I64)).map_err(|_| ())
            } ]
        }
        BigInt {
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
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

        PNew . ^[xs].p:[Name* -> Proc]
        |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;

        // customize error handling
        // (e.g. filter results by =/= Err)
        Err . |- "error" : Proc;

        // cast rust-native types as processes
        // Order matters for literals: more specific integer kinds (u32, BigInt) before i64 Int
        // so tokens like `1n` / `1u32` are not rejected by the Int prefix arm.
        CastBigRat . r:BigRat |- r : Proc;
        CastFixed . x:Fixed |- x : Proc;
        CastFloat . k:Float |- k : Proc;
        CastBigInt . n:BigInt |- n : Proc;
        CastUInt32 . u:UInt32 |- u : Proc;
        CastInt . k:Int |- k : Proc;
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
        // or/and, then comparisons, then arithmetic — so `a/b == c/d` and `x==y and z==w` parse correctly.
        Or . a:Proc, b:Proc |- a "or" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x || *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        And . a:Proc, b:Proc |- a "and" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x && *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
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
                _ => Proc::Err,
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
                _ => Proc::Err,
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
                _ => Proc::Err,
            }}
        ] fold;

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
                _ => {
                    if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(&a, &b) {
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
                _ => {
                    if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(&a, &b) {
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
                _ => Proc::Err,
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
                _ => Proc::Err,
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
                _ => Proc::Err,
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
                _ => Proc::Err,
            }}
        ] fold;

        // Arithmetic (tighter than == and and/or)
        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone() + (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x + y))),
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
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone() + (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x + *y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(format!("{}{}", x, y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone() - (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x - y))),
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
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone() - (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x - *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone() * (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x * y))),
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
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone() * (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(*x * *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Div . a:Proc, b:Proc |- a "/" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone() / (**b).clone())),
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
                    // arms below); without this guard `0.0 / 0.0` canonicalizes its NaN to `0`.
                    (Float::FloatLit(_), Float::FloatLit(y)) => {
                        if y.get() == 0.0 { Proc::Err } else { Proc::CastFloat(std::sync::Arc::new((**a).clone() / (**b).clone())) }
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
                _ => Proc::Err,
            }}
        ] fold;

        Mod . a:Proc, b:Proc |- a "%" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone() % (**b).clone())),
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
                _ => Proc::Err,
            }}
        ] fold;

        NegProc . a:Proc |- "-" a : Proc ![
            { match &a {
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(n) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(-n))),
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
                _ => Proc::Err,
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

        MToByteArray . m:Proc
        |- m "." "toByteArray" "(" ")" : Proc ![{
            match &m {
                Proc::CastList(_) | Proc::CastMap(_) | Proc::CastSet(_) | Proc::CastBag(_) => {
                    crate::rhocalc::wire::collection_to_byte_array_proc(m)
                        .unwrap_or(Proc::Err)
                },
                _ => Proc::Err,
            }
        }] fold;

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

        LNth . l:Proc, i:Proc
        |- l "." "nth" "(" i ")" : Proc ![{
            match (&l, &i) {
                (Proc::CastList(lit), Proc::CastInt(ii)) => match (lit.as_ref(), &**ii) {
                    (List::ListLit(v), Int::NumLit(n)) => {
                        v.get(*n as usize).cloned().expect("at: index out of bounds")
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
                _ => Proc::Err,
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
