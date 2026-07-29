// Task #101 — FIXTURE 3. See `languages/tests/collection_fold_carriers.rs` for the assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// TuringLoop — a MULTI-STEP machine, so "the head moves" is not a claim about
//              a derivation of length two.
//
// The production spec `languages/src/turing.rs` transcribes the GSLT omnibus paper's
// transition table verbatim, and that table has entries only from `q0`, with `D_q0_0` landing
// in `q1`. Its maximal derivation is therefore EXACTLY two firings: the transition, then the
// head move it names. That is the honest statement of the repair for that spec, and
// `languages/tests/turing.rs` makes it — but two firings cannot distinguish "the head moves"
// from "the head moves once and then something re-freezes".
//
// This grammar is the production spec's `types` / `terms` verbatim (the same zipper `Tp`, the
// same `shift_right` helper with the same `![…]` body) plus TWO EXTRA TABLE ENTRIES, from `q1`
// and `q2`. Nothing in `languages/src/turing.rs` is touched: adding table entries is a change
// to the THEORY, and the paper's theory is what that file transcribes.
//
// Run from `(q0 , <[] | 0 | [0,0]>)` the machine takes three transitions and three head moves:
//
//   step │ state │ tape before                 │ head move                    │ tape after
//   ─────┼───────┼─────────────────────────────┼──────────────────────────────┼─────────────────
//    1   │ q0    │ `<[]      | 0 | [0,0]>`     │ `shift_right([],1,[0,0])`    │ `<[1]     | 0 | [0]>`
//    2   │ q1    │ `<[1]     | 0 | [0]>`       │ `shift_right([1],1,[0])`     │ `<[1,1]   | 0 | []>`
//    3   │ q2    │ `<[1,1]   | 0 | []>`        │ `shift_right([1,1],1,[])`    │ `<[1,1,1] | _ | []>`
//
// The third move exercises the helper's `None` branch (`r.split_first()` on an empty right
// context yields `Sym::Blank`), so the fold body is executed on both of its arms across the
// run rather than only the easy one.
language! {
    name: TuringLoop,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        hosted_in: "tests/definitions/turing_loop.rs",
    },

    types {
        Config
        Tape
        State
        Sym
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

        Q0 . State ::= "q0" ;
        Q1 . State ::= "q1" ;
        Q2 . State ::= "q2" ;
        Q3 . State ::= "q3" ;

        Tp . l:Vec(Sym), h:Sym, r:Vec(Sym)
            |- "<" "[" l.*sep(",") "]" "|" h "|" "[" r.*sep(",") "]" ">" : Tape ;

        Cf . q:State, t:Tape |- "(" q "," t ")" : Config ;

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
        // The production spec's own entry, verbatim.
        D_q0_0 . |- (Cf Q0 (Tp L Zero R))
                    ~> (Cf Q1 (shift_right L One R));
        D_q0_1 . |- (Cf Q0 (Tp L One R))
                    ~> (Cf Halt (Tp L One R));

        // ➕ the two extra entries that make the run multi-step.
        D_q1_0 . |- (Cf Q1 (Tp L Zero R))
                    ~> (Cf Q2 (shift_right L One R));
        D_q2_0 . |- (Cf Q2 (Tp L Zero R))
                    ~> (Cf Q3 (shift_right L One R));
    },
}
