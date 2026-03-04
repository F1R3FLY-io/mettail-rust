# ExecEq (*@P = P) Infinite Loop

**Date**: 2026-03  
**Status**: Resolved via normalization (no matching axiom)  
**Related**: `languages/src/rhocalc.rs`, `macros/src/logic/rules.rs`, `macros/src/logic/mod.rs`

---

## Problem

Adding the equation **ExecEq**: `(PDrop (NQuote P)) = P` (*@P = P) causes the Ascent fixpoint to loop infinitely.

## Root Cause

1. **Equation rule** (from `rules.rs`): For `proc(s)` with `s = *@P`, we derive `eq_proc(*@P, P)` and add **`proc(P)`**.
2. **Eqrel**: Equality closes under **symmetry**, so we get `eq_proc(P, *@P)`.
3. **Name congruence**: `eq_proc(P, *@P)` implies `eq_name(@(P), @(*@(P)))`.
4. **PDrop congruence**: `eq_name(@(P), @(*@(P)))` implies `eq_proc(*@(P), *@(*@(P)))`.
5. **Exec rewrite**: We get `rw_proc(*@(*@(P)), *@(P))`.
6. **Rewrite closure** (in `logic/mod.rs`):  
   `rw_proc(a, c) <-- eq_proc(a, b), rw_proc(b, c)`  
   So we get `rw_proc(*@(P), *@(*@(P)))` and then `rw_proc(P, *@(*@(P)))`.
7. **Category exploration**: `proc(c1) <-- proc(c0), rw_proc(c0, c1)` adds **`proc(*@(*@(P)))`**.
8. The same cycle then produces `proc(*@(*@(*@(P))))`, and so on → **unbounded growth** and non-termination.

## Solution: Normalize only (no ExecEq, no matching axiom)

Implemented on branch `no_extra_congruences`:

1. **`Proc::normalize()`** (macro `term_ops/normalize.rs`): For `PDrop(Name)`, when the name is `NQuote(p)`, return `p.normalize()` so *@P reduces to P.
2. **Seed and exploration**: When pushing to `proc` (seed in `language.rs`, exploration in `categories.rs`), use `t.normalize()` for Proc so we only store canonical forms.
3. **Fewer congruences**: Only ParCong and NewCong are kept in rhocalc; Add/Sub/Mul/Div/Eq/... congruences are removed (normalization makes them unnecessary for *@P).

We do **not** add ExecEq as an equation. We do **not** use a matching axiom `eq_proc(p, *@(p)) <-- proc(p)` (it caused the fixpoint to hang). With normalization alone, Comm's RHS (e.g. *@(2)+*@(3)) is stored as `2+3`, so we get the right result without needing Exec to fire or extra equations.
