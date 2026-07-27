// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
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
// twin of the Rholang `Comm` rule (`CommDemo`): the SAME non-linear AC firing shape MINUS the
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
// nullary leaves (`Na`/`Nb` = `na`/`nb`) and processes distinct nullary leaves (`PA`/`PB` = `A`/`B`),
// so distinct names/processes are available for the positive (matching) and negative (mismatched)
// firing checks, and neither leaf spelling collides with the auto-generated lowercase `a` VARIABLE
// identifier — so a name-variable ambient `a[·]` still round-trips through parse ∘ display.
//
// The concrete redex `{ open(na, A) | na[B] }` reduces (both names `na`) to `{ A | B }` — the
// unwrapped `P = A` and `Q = B` in parallel — and `{ open(na, A) | na[B] } ≠ { A | B }`, so a
// positive OUT observation of `{ A | B }` is non-vacuous evidence the Ambient `OpenRule` fired as
// ONE COMM with the σ Dovetail computed. The mismatched soup `{ open(na, A) | nb[B] }` (names
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
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `ambdemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_ambdemo_*.rs`, whose `use mettail_languages::ambdemo::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/ambdemo.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc ;

        // Distinct nullary processes `A`/`B` — the payloads `open(n, ·)` dissolves and `n[·]`
        // ambient carries. Spelled with CAPITAL letters (like the sibling `SwapDemo`/`CtxDemo`/
        // `AcDemo` process leaves `A`/`B`/`C`) so they do NOT collide with the auto-generated,
        // lowercase process/name VARIABLE identifiers (`PVar`/`NVar`, spelled `a`). A lowercase
        // literal `"a"` would RESERVE the token `a`, so a `PAmb`/`POpen` whose ambient name is a
        // variable — displayed as e.g. `a[A]` — could not re-parse: the lexer would grab the leading
        // `a` as the `PA` literal (a complete `Proc`) and choke on the following `[`. Kept nullary
        // (single leaf literals) so `{ A | B }` decodes to a bag of two distinct tagged leaves for
        // the positive firing check; the structural-restructuring semantics (unwrap-and-splice) are
        // unchanged by their arity.
        PA . |- "A" : Proc ;
        PB . |- "B" : Proc ;

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
