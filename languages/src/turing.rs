//! GSLT omnibus conformance — **L9 `Turing`** (`omnibus.tex:1900-1936`): a
//! single-tape Turing machine as a GSLT, used by the paper as its *non*-example
//! of interactivity (:692-720, :1938-1942).
//!
//! # Why this file lives in `languages/src/`
//!
//! The language specifications transcribed from the GSLT omnibus paper are
//! PRODUCTION specs (USER ruling, 2026-07-27), so they live beside the other
//! production languages in `languages/src/` and are reachable through the
//! crate's public surface as `mettail_languages::turing`. Its conformance suite
//! is `languages/tests/turing.rs` — the same spec/tests split every other
//! production spec uses (`languages/src/calculator.rs` ↔
//! `languages/tests/calculator.rs`). That suite's own header records why the
//! dynamics are proven from `dovetail_report_for` firings rather than from a
//! reconstructed normal form.
//!
//! `emit_tests` / `emit_simulator` / `emit_blockly` stay OFF. Those three
//! options are the macro's file-writing switches, so with them off this spec
//! writes no `languages/tests/gen_turing_*.rs`, no
//! `languages/src/bin/simulate_turing.rs` and no
//! `languages/src/generated/turing-*.ts`; the conformance statements this theory
//! has to make are the hand-written ones next door.
//!
//! ⚠ Those three `false`s must STAY false, and not because production specs are
//! forbidden generated suites — `ambient`/`calculator`/`lambda`/`rhocalc` all
//! carry theirs. `emit_simulator: true` would make the macro write
//! `languages/src/bin/simulate_turing.rs` on every compile, and cargo's edition-2021
//! auto-discovery would pick that file up as a binary target with NO
//! `required-features = ["strategies"]` — every hand-declared `[[bin]]` in
//! `languages/Cargo.toml` carries that gate because the generated simulator names
//! `mettail_languages::turing::strategies::arb_*`, which exists only under the
//! `strategies` feature. A default `cargo build -p languages` would then fail to
//! compile a file nobody wrote. Flipping these on is a change to the macro's
//! emission contract, not a per-language switch.
//!
//! # Clause-by-clause containment (SUPERSET of the omnibus listing)
//!
//! | omnibus clause (`omnibus.tex`) | our clause | delta |
//! | --- | --- | --- |
//! | `types { Config Tape State Sym }` (:1904-1909) | identical + `![u32] as UInt32` | ➕ the carrier `Q` needs |
//! | `Blank . Sym ::= "_" ;` (:1912) | identical | — |
//! | `Zero . Sym ::= "0" ;` (:1913) | identical | — |
//! | `One . Sym ::= "1" ;` (:1914) | identical | — |
//! | `Halt . State ::= "halt" ;` (:1916) | identical | — |
//! | `Q . n:UInt32 \|- "q" n : State ;` (:1917) | identical | — |
//! | `Tp . l:List(Sym), h:Sym, r:List(Sym) \|- "<" l "\|" h "\|" r ">" : Tape ;` (:1920) | `l:Vec(Sym) … "<" "[" l.*sep(",") "]" "\|" h "\|" "[" r.*sep(",") "]" ">"` | `List(X)` → `Vec(X)`; explicit list delimiters |
//! | `Cf . q:State, t:Tape \|- "(" q "," t ")" : Config ;` (:1922) | identical | — |
//! | `D_q0_0 . \|- (Cf (Q 0u32) (Tp L Zero R)) ~> (Cf (Q 1u32) (shift_right L One R));` (:1930-1931) | `D_q0_0 . \|- (Cf Q0 (Tp L Zero R)) ~> (Cf Q1 (shift_right L One R));` | state written as a nullary constant — see ★ below |
//! | `D_q0_1 . \|- (Cf (Q 0u32) (Tp L One R)) ~> (Cf Halt (Tp L One R));` (:1932-1933) | `D_q0_1 . \|- (Cf Q0 (Tp L One R)) ~> (Cf Halt (Tp L One R));` | idem |
//! | `equations { }` (:1925) | identical (empty) | — |
//!
//!
//! # Notation: the paper is BNFC-flavoured; this file is idiomatic mettail
//!
//! The omnibus's listings carry a labelled-BNF (BNFC) lineage — `Label . Cat ::=
//! "lit" Item … ;` productions and a parameterised `List(X)` carrier. mettail
//! accepts the `::=` form (and this file uses it for nullary constants, exactly as
//! `languages/src/ambient.rs` does), but its idiomatic form is the JUDGEMENT form
//! `Name . ctx |- pattern : Cat ;`, and `List(X)` is spelled `Vec(X)` (the
//! established convention — `rhocalc.rs:57` declares `![Vec<Proc>] as List`).
//! **Superset containment here is SEMANTIC**: every `types` entry, `terms`
//! production, `equations` clause and `rewrites` rule of the paper's version is
//! present with the same meaning; the spelling is ours. Every deviation is
//! tabulated above and explained below.
//!
//! ## ★ The one FORCED delta: native literals are not expressible in patterns
//!
//! The paper's transition entries embed the typed literals `(Q 0u32)` / `(Q 1u32)`
//! **inside a rewrite pattern**. The live macro's pattern grammar has no literal
//! form: `parse_pattern` (`ast/src/language/parse.rs:2836-3007`) accepts exactly
//! metasyntax (`*zip`/`*map`), a `{…, ...rest}` collection, a parenthesised
//! constructor application, a `^x.` binder, or a bare identifier — and
//! `PatternTerm` (`ast/src/pattern.rs:25-49`) has variants `Var`, `Apply`,
//! `Lambda`, `MultiLambda`, `Subst`, `MultiSubst` and **no literal variant**. So
//! `(Q 0u32)` fails at macro-parse time (`0u32` is not an identifier). This is a
//! genuine macro limitation, reported rather than silently worked around.
//!
//! The transition *semantics* are preserved exactly by naming the two machine
//! states with nullary constructors `Q0`/`Q1` (surface `q0`/`q1` — the very
//! surface the paper's own CFL program writes at :1949, `work!( (q0 , …) )`), so
//! the two table entries fire on precisely the configurations the paper
//! specifies. `Q . n:UInt32 |- "q" n : State ;` is ALSO declared, verbatim, so
//! the doc clause itself is present; `Q0`/`Q1` are additional (superset) clauses
//! that give the pattern language something it can name. A bare identifier that
//! resolves to a declared nullary rule is read as that constructor, not as a
//! metavariable (`ast/src/pattern.rs:382-398`, `1944-1962`).
//!
//!
//! ## `shift_right` — the paper's "theory-supplied helper"
//!
//! `(shift_right L One R)` appears in the paper's RHS (:1931) with no declaration.
//! The macro special-cases exactly one builtin RHS operation, `eval` (the
//! substitution operator); every other head must resolve to a declared rule label
//! or the validator rejects it (`ast/src/validation/error.rs`, `"Unknown
//! constructor"`). We therefore give it a home as a declared `Tape`-valued term
//! former with a native `fold` body:
//!
//! ```text
//! shift_right(l, h, r)  ≙  Tp( h : l ,  head(r) or Blank ,  tail(r) )
//! ```
//!
//! i.e. *write `h` at the head cell and move right* — the exact operation the
//! paper's comment describes ("q0 reading 0: write 1, move right, go to q1"),
//! over the zipper representation ("reversed left context, head symbol, right
//! context", :1919). The helper is spelled `shift_right` verbatim, so the RHS
//! reads exactly as printed in the paper.

#![allow(
    non_local_definitions,
    non_camel_case_types,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    unused_imports,
    dead_code
)]

use mettail_macros::language;

language! {
    name: Turing,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Config
        Tape
        State
        Sym
        // Carrier for the paper's `n:UInt32` state index.
        ![u32] as UInt32
    },

    literals {
        UInt32 {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)u32";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
    },

    terms {
        Blank . Sym ::= "_" ;
        Zero . Sym ::= "0" ;
        One . Sym ::= "1" ;

        Halt . State ::= "halt" ;
        Q . n:UInt32 |- "q" n : State ;

        // ➕ (ours) The two machine states of the paper's transition table as
        // nullary constants, so the table entries below can name them in a
        // pattern (no literal pattern form exists — see the module header).
        Q0 . State ::= "q0" ;
        Q1 . State ::= "q1" ;

        // tape as a zipper: reversed left context, head symbol, right context
        Tp . l:Vec(Sym), h:Sym, r:Vec(Sym)
            |- "<" "[" l.*sep(",") "]" "|" h "|" "[" r.*sep(",") "]" ">" : Tape ;

        Cf . q:State, t:Tape |- "(" q "," t ")" : Config ;

        // ➕ (ours) the paper's theory-supplied helper, given a home:
        // write `h` at the head cell, then move right.
        shift_right . l:Vec(Sym), h:Sym, r:Vec(Sym)
            |- "shift_right" "(" "[" l.*sep(",") "]" "," h "," "[" r.*sep(",") "]" ")" : Tape ![{
                let mut left: Vec<Sym> = Vec::with_capacity(l.len());
                left.push(h.clone());
                left.extend(l.iter().cloned());
                let (head, rest): (Sym, Vec<Sym>) = match r.split_first() {
                    Some((s, tail)) => (s.clone(), tail.to_vec()),
                    None => (Sym::Blank, Vec::new()),
                };
                Tape::Tp(left, std::sync::Arc::new(head), rest)
            }] fold;
    },

    equations { },

    rewrites {
        // one entry of the transition table, written out
        // q0 reading 0: write 1, move right, go to q1
        D_q0_0 . |- (Cf Q0 (Tp L Zero R))
                    ~> (Cf Q1 (shift_right L One R));
        D_q0_1 . |- (Cf Q0 (Tp L One R))
                    ~> (Cf Halt (Tp L One R));
    },
}
