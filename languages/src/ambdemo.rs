#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 3d demonstration language: the Ambient-calculus `OpenRule`
//
//     OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest})
//
// i.e. `open(n, P) | n[Q]  ~>  P | Q`, spliced back into the residual bag. It is the STRUCTURAL
// twin of the RhoCalc `Comm` rule (`CommDemo`): the SAME non-linear AC firing shape MINUS the
// substitution. It composes, in ONE atomic COMM on the live f1r3node reducer:
//
//   * a HashBag AC match over `PPar` with k=2 STRUCTURED fixed elements — the capability `POpen N P`
//     (`open(n, P)`) and the ambient `PAmb N Q` (`n[Q]`) — + `...rest`, the order-independent
//     process-soup carrier (`AcBagDemo`'s `reflect_hashbag_soup_par`, tag-routed element patterns);
//   * a NON-LINEAR consistency guard: the ambient name `N` occurs in BOTH structured elements, so
//     each occurrence binds a DISTINCT σ slot (a Rholang pattern free variable may occur at most
//     once), and the installed receiver's `Receive.condition` `EEq(N_open, N_amb)` — the
//     `where`-clause the reducer commits the COMM under only when it evaluates to `GBool(true)` —
//     enforces `N ≡ N`, reject-safe (a mismatched-name soup `open(n, P) | m[Q]` leaves the data
//     resting, so `open` cannot dissolve a NON-matching ambient);
//   * a PURE STRUCTURAL reduct: UNLIKE `Comm` (whose reduct is the host-computed substitution
//     `cont[Q/y]`, delivered as the firing's contractum), `OpenRule` unwraps `P` from `open(n, P)`
//     and `Q` from `n[Q]` and splices `{P, Q, ...rest}`. Both `P` and `Q` are LHS-element arguments,
//     so the firing's σ already carries them (`is_structural_ac_rewrite`/`structural_ac_rule_shape`);
//     the σ-injection recovers them DIRECTLY from σ (there is no host computation), and the receiver
//     body emits the bag RHS `@"ac:PPar"!(P) | @"ac:PPar"!(Q) | rest`.
//
// `POpen . n:Name, p:Proc` is the ambient-dissolution capability `open(n, p)`; `PAmb . n:Name,
// p:Proc` is the ambient `n[p]`; both carry the ambient name `n` and a process. Names are distinct
// nullary leaves (`Na`/`Nb`) and processes distinct nullary leaves (`PA`/`PB`), so distinct
// names/processes are available for the positive (matching) and negative (mismatched) firing checks
// without single-letter identifiers colliding.
//
// The concrete redex `{ open(na, a) | na[b] }` reduces (both names `na`) to `{ a | b }` — the
// unwrapped `P = a` and `Q = b` in parallel — and `{ open(na, a) | na[b] } ≠ { a | b }`, so a
// positive OUT observation of `{ a | b }` is non-vacuous evidence the Ambient `OpenRule` fired as
// ONE COMM with the σ Dovetail computed. The mismatched soup `{ open(na, a) | nb[b] }` (names
// `na` ≠ `nb`) does NOT fire — the non-linear `Receive.condition` vetoes it.
//
// Kept SEPARATE from the full `Ambient` (whose `InRule`/`OutRule` are DEEP nested-ambient AC
// reductions, and whose `PNew ^x` binder + `new`-floating structural-congruence equations require
// the untyped path's binder-congruence float) so the CLEAN structural-AC communication is isolated
// exactly as `SwapDemo`/`AcDemo`/`AcBagDemo`/`CtxDemo`/`LambdaDemo`/`NativeDemo`/`CommDemo` isolate
// their respective firing families. `Ambient`'s `InRule`/`OutRule` stay `Unsupported` (fail-closed)
// on the Rho backend; this demo proves the OpenRule half fires end-to-end.
language! {
    name: AmbDemo,

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

        // Distinct nullary processes `a`/`b` — the payloads `open(n, ·)` dissolves and `n[·]`
        // ambient carries. Kept nullary (single leaf literals) so `{ a | b }` decodes to a bag of
        // two distinct tagged leaves for the positive firing check; the structural-restructuring
        // semantics (unwrap-and-splice) are unchanged by their arity.
        PA . |- "a" : Proc ;
        PB . |- "b" : Proc ;

        // Distinct nullary ambient names `na`/`nb` for the matching / mismatched name checks.
        Na . |- "na" : Name ;
        Nb . |- "nb" : Name ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

        // The ambient-dissolution capability `open(n, p)` and the ambient `n[p]`. Both carry the
        // ambient name `n` (the non-linear channel `OpenRule` matches on) and a process.
        POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc ;

        PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
    },

    equations {},

    rewrites {
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P, Q, ...rest}) ;
    },
}
