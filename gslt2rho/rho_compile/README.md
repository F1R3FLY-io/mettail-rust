# `rho_compile`

Compile a MeTTaIL GSLT specification to rho-calculus terms via
set-automaton-driven optimal channel naming.

This crate is the runtime companion to the paper *Optimal Channel Naming
for Compositional Rewrite Translations via Set Automaton Partial
Evaluation* (`optimal-channels.pdf`).

## What it does

Given the `rewrites { ... }` portion of a MeTTaIL `language!` block, this
crate produces an equivalent rho-calculus program in which:

1. Each direct rewrite `L ~> R` becomes a persistent for-receive that
   matches `L` and emits `R` on a dedicated channel.
2. Each contextual rewrite
   `S_1 ~> T_1, ..., S_n ~> T_n => K(...) ~> K'(...)` becomes a
   persistent for-receive on the channel `tc(K)`, where `tc(K)` is
   computed by partial evaluation of a Bouwman--Erkens set automaton
   (constructed once, off-line, from the union of all LHSs) on the
   surface of `K`.

The channel-naming function `tc(·)` is **optimal** in three precise senses:

- **(O1) Symbol-once.** Each surface symbol of an outer context is
  consumed by exactly one for-receive in the compiled rho process.
- **(O2) Prune-preserves.** Inner reductions never invalidate outer
  channels; the for-receives surrounding a hole stay live across firings.
- **(O3) Coarsest sound.** Two contexts the matcher cannot distinguish
  share a channel; two contexts the matcher distinguishes get distinct
  channels.

## Pipeline

```
   Gslt   --[ build set automaton ]-->   SetAutomaton
     \                                   /
      \         [ for each rule ]      /
       v                              v
     compile_rule  -- tc(K) -->   Proc (rho)
```

## Modules

| Module        | Role                                                                                           |
|---------------|------------------------------------------------------------------------------------------------|
| `gslt`        | Input AST: rewrite rules and contextual rewrites.                                              |
| `rho`         | Output AST: the `RhoCalc` language as defined in the MeTTaIL README.                          |
| `automaton`   | Set-automaton construction (Bouwman--Erkens, arXiv:2202.08687).                                |
| `channel`     | Computation of `tc(K)` via partial evaluation of the automaton on `K`.                         |
| `compile`     | Glue: GSLT in, parallel composition of compiled rho processes out.                             |

## Quick start

```bash
cargo test                          # 15 unit tests
cargo run --example lambda_head     # §6.1 of the paper
cargo run --example rho_into_rho    # §6.2 of the paper
```

## Integration with `mettail-rust`

This crate is designed as a workspace member that consumes the parsed
form of a `language!` macro invocation. To wire it into the existing
mettail-rust pipeline:

1. In `macros/`, after parsing the `rewrites { ... }` section, construct
   a `gslt::Gslt` value via the appropriate adapter.
2. Call `rho_compile::compile(&gslt)` to obtain a `CompiledGslt`.
3. Either embed the resulting rho processes alongside the existing
   ascent-based rewrite engine (as a parallel "rho target") or use them
   as the canonical run-time, depending on the desired backend strategy.

The output `Proc` AST mirrors the `RhoCalc` language exactly, so it can
be fed to MeTTaIL's existing rho-calculus printer/serialiser without
adaptation.

## Caveats

The current implementation:

- Supports left-linear LHS patterns only; non-linear support per §5
  of the paper is sketched but not yet emitted (the binders are
  deduplicated, with a TODO marker for the consistency-receive
  elaboration).
- Treats both true holes and schema variables as suspension points, but
  distinguishes them in the channel reflection so that `Par_L` and
  `Par_R`-style rules receive distinct channels. See `channel::BudKind`.
- Builds the automaton from a closed rule set; dynamic rule introduction
  per §7 of the paper requires incremental automaton update, which is
  future work.

## Files

```
src/
  lib.rs        public API
  gslt.rs       GSLT input AST
  rho.rs        rho output AST  (matches MeTTaIL RhoCalc)
  automaton.rs  Bouwman-Erkens set automaton
  channel.rs    tc(K) computation
  compile.rs    main compiler

examples/
  lambda_head.rs    Lambda calculus, head-context reduction (§6.1)
  rho_into_rho.rs   The rho calculus, into itself (§6.2)
```
