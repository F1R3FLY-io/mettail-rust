#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 4 (Ambient In/Out) demonstration language: the Ambient-calculus `InRule` + `OutRule` —
// DEPTH-2 NESTED structural non-linear AC reductions — fired IN RHO as ONE atomic COMM on the live
// f1r3node reducer. This GENERALIZES the just-landed `AmbDemo` `OpenRule` (a DEPTH-1 flat structural
// AC firing) to a NESTED element whose argument is itself a HashBag, with a CROSS-LEVEL non-linear
// equality.
//
//     InRule  . { n[{ in(m, P), ...q }], m[R], ...s } ~> { m[{ n[{ P, ...q }], R }], ...s }
//     OutRule . m[{ n[{ out(m, P), ...q }], R, ...s }] ~> { n[{ P, ...q }], m[R], ...s }
//
// i.e. `n[{in(m,P) | q}] | m[R]  ~>  m[{n[{P | q}] | R}]` (an ambient `n` carrying an `in m`
// capability MOVES INTO the sibling ambient `m`), and its dual `m[{n[{out(m,P) | q}] | R}]  ~>
// n[{P | q}] | m[R]` (the ambient `n` carrying an `out m` capability MOVES OUT of `m`). Both compose,
// in ONE atomic COMM on the reducer:
//
//   * a DEPTH-2 nested HashBag AC match: the outer operand bag matches `k = 2` structured elements —
//     the NESTED ambient `n[{in(m,P), ...q}]` (`PAmb N (PPar {…})`, whose second argument is itself a
//     HashBag carrying the capability `in(m,P)`) and the plain ambient `m[R]` (`PAmb M R`) — plus the
//     outer process-soup remainder `...s`; the reducer's `SpatialMatcher<Par,Par>` recurses
//     `Par→Send→EList→Par→Send` into the inner bag (`reflect_ground_term_par` routes a HashBag
//     ARGUMENT to the same order-independent process-soup carrier as the top bag), so the inner
//     capability + inner remainder `...q` bind ONE level down in the SAME atomic `consume` — no depth
//     cap;
//   * a CROSS-LEVEL NON-LINEAR consistency guard: the ambient name `M` occurs BOTH one level down (in
//     `in(m,P)`, the INNER capability's channel) AND at the outer level (in `m[R]`, the sibling
//     ambient's channel), so each occurrence binds a DISTINCT σ slot (a Rholang pattern free variable
//     may occur at most once), and the installed receiver's `Receive.condition` `EEq(M_outer,
//     M_inner)` — the `where`-clause the reducer commits the COMM under only when it evaluates to
//     `GBool(true)` — enforces `M ≡ M`, reject-safe: a mismatched-name soup `n[{in(m,P)}] | k[R]`
//     (with `k ≠ m`) leaves the data resting, so the `in` capability cannot enter a NON-matching
//     ambient. The guard is DEPTH-AGNOSTIC — the reducer flattens every free variable at every nesting
//     depth into ONE De Bruijn frame (`free_map`), so the guard compares an outer-bound slot against
//     an inner-bound slot freely (`aggregate_updates` PANICS on a repeated free level, which is
//     precisely why the two `M` occurrences must be DISTINCT slots joined by the `EEq` guard, not a
//     single repeated pattern variable);
//   * a NESTED STRUCTURAL reduct: UNLIKE `OpenRule` (whose reducts `P`/`Q` are bare LHS-element
//     arguments the σ carries DIRECTLY), the In/Out reduct `m[{n[{P | q}] | R}]` is a re-assembled
//     NESTED restructuring of the matched sub-terms. It is the firing's contractum `RHS[σ]`, which the
//     host Dovetail engine computes from the AC-matched σ (binding `N`, `M`, `P`, the inner remainder
//     `q`, `R`, and the outer remainder `s`); the σ-injection reflects the WHOLE nested reduct element
//     and delivers it as the single host-σ-sourced value, and the receiver body splices
//     `@"ac:PPar"!(reduct) | s` on `@out`. The nested bag PATTERN (verifying the depth-2 shape + the
//     cross-level guard + binding the outer remainder `s`) is the new mechanism; the firing seam
//     (`structural_ac_contract_call`, `channel!(⟦bag⟧, ⟦reduct⟧, @out)`) is REUSED from `OpenRule`
//     with the single (`m = 1`) nested reduct.
//
// The concrete `InRule` redex `{ na[{ in(nb, A) }] | nb[B] }` (the outer ambient `na`, the `in`
// capability's target AND the sibling ambient BOTH `nb`) reduces to `{ nb[{ na[{ A }] | B }] }` — the
// `na` ambient (carrying `A`) moved INTO the `nb` ambient (carrying `B`) — and `{ na[{ in(nb, A) }] |
// nb[B] } ≠ { nb[{ na[{ A }] | B }] }`, so a positive OUT observation of the restructured bag is
// non-vacuous evidence the Ambient `InRule` fired as ONE COMM with the σ Dovetail computed. The
// mismatched soup `{ na[{ in(nb, A) }] | nc[B] }` (the `in` target `nb` ≠ the sibling ambient `nc`)
// does NOT fire — the cross-level non-linear `Receive.condition` vetoes it. The dual `OutRule` redex
// `nb[{ na[{ out(nb, A) }] | B }]` reduces to `{ na[{ A }] | nb[B] }`.
//
// Distinct nullary processes `A`/`B` (the payloads the capabilities carry) are spelled with CAPITAL
// letters (like the sibling `AmbDemo`/`SwapDemo` process leaves) so they do NOT collide with the
// auto-generated lowercase process/name VARIABLE identifiers, and distinct nullary ambient names
// `na`/`nb`/`nc` supply the matching / mismatched cross-level name checks.
//
// Kept SEPARATE from `AmbDemo` (whose only rewrite is the flat `OpenRule`, and whose
// `rho_net_structural_ac_injection_sites` asserts exactly ONE site) and from the full `Ambient`
// (whose `PNew ^x` binder + `new`-floating structural-congruence equations require the untyped path's
// binder-congruence float) so the CLEAN depth-2 nested-AC In/Out communication is isolated exactly as
// `SwapDemo`/`AcDemo`/`AcBagDemo`/`CtxDemo`/`LambdaDemo`/`NativeDemo`/`CommDemo`/`AmbDemo` isolate
// their respective firing families. With empty `equations {}` there is no `PNew` binder, so
// `should_emit_binder_congruence` is `false` and the language routes to the TYPED native lane (exactly
// like `AmbDemo`), where `dovetail_report_for` produces the In/Out justification σ + contractum the
// structural-AC σ-injection reads.
language! {
    name: InOutDemo,

    options {
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc ;

        // Distinct nullary processes `A`/`B` — the payloads the `in`/`out` capabilities carry and the
        // ambients hold. CAPITALIZED so they do NOT collide with the auto-generated lowercase
        // process/name VARIABLE identifiers (`PVar`/`NVar`, spelled `a`). Kept nullary (single leaf
        // literals) so a restructured bag decodes to distinct tagged leaves for the positive firing
        // check; the nested-restructuring semantics are unchanged by their arity.
        PA . |- "A" : Proc ;
        PB . |- "B" : Proc ;

        // Distinct nullary ambient names `na`/`nb`/`nc` for the cross-level matching / mismatched
        // name checks. `na` is the OUTER (moving) ambient; `nb` is the shared cross-level name `M`
        // (the `in`/`out` target AND the sibling / root ambient) in a MATCHING redex; `nc` supplies
        // the mismatched sibling ambient in the NEGATIVE check.
        Na . |- "na" : Name ;
        Nb . |- "nb" : Name ;
        Nc . |- "nc" : Name ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

        // The `in(n, p)` / `out(n, p)` ambient-movement capabilities and the ambient `n[p]`. Each
        // capability carries the target ambient name `n` (the cross-level non-linear channel the
        // In/Out rules match on) and a process `p`; the ambient carries its name `n` and a process.
        PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc ;
        POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc ;

        PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
    },

    equations {},

    rewrites {
        // { n[{ in(m, P), ...q }], m[R], ...s } ~> { m[{ n[{ P, ...q }], R }], ...s }
        InRule . |- (PPar {(PAmb N (PPar {(PIn M P), ...rest1})), (PAmb M R), ...rest2})
            ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2}) ;

        // m[{ n[{ out(m, P), ...q }], R, ...s }] ~> { n[{ P, ...q }], m[R], ...s }
        OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
            ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2}) ;
    },
}
