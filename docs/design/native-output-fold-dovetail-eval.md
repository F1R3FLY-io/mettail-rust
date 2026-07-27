# Native-Output Fold Evaluation on the Dovetail Typed-Fold Path

**Target:** branch `feature/wfst-architecture`. Closes the post-P6 gap where native-output
folds (Calculator arithmetic `AddInt(1,2)→3`, etc.) stopped evaluating after Ascent retired.
**Status:** design complete (Plan agent, empirically verified); implementation in progress (foreground).

## Principle (user directive)

Dovetail completes all the rewrites it can — native-output folds (arithmetic), non-native-output
casts (already working for rholang), structural rewrites. The Rho machine (f1r3node `RhoRuntime`/
`DebruijnInterpreter` + RSpace, via `rholang-runtime`) is dispatched **only when Rho-process
semantics are needed** (COMM/channels). Per-language `selected_default_runtime_backend` is the
dispatch seam: rewrite-only languages (Calculator) advertise Dovetail; Rho languages advertise the
Rho machine. This change makes Dovetail actually complete the Calculator rewrites it claims.

## Corrected diagnosis (verified empirically by the Plan agent)

The earlier framing ("Calculator is on the plain `EGraph<String>` path") was **wrong**:
- Calculator is ALREADY on the typed-`L` path — `needs_typed_fold_path` returns true because it has
  `Proc`-output folds (`ElemList`/`GetMap`, calculator.rs:402/417; `Proc` has no native type).
- The real gap: `collect_fold_rules` (typed_report.rs:89-93) `continue`-skips folds where NO param
  is non-Scalar: `if !all_simple || !params.iter().any(|p| !matches!(p.bind, BindKind::Scalar)) { continue; }`.
  `AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;` has both params `Scalar` (Int has native
  type i32), so it is skipped — never emitted as a `NativeRule`, dispatcher gets no arm, never fires.
  Same for Sub/Mul/Div/Mod/Neg/BitAnd…, all UInt32/BigInt/BigRat/Fixed/Float folds, CustomOp.
- Empirical: Dovetail report for `1 + 2` = `AddInt`,`NumLit(1)`,`NumLit(2)` + cross-cat casts, NO `NumLit(3)`.

## §1 — Codegen fix (shared, universal; not Calculator-specific)

All in `macros/src/gen/runtime/dovetail_report/typed_report.rs`:

- **§1a** widen the `collect_fold_rules` gate (89-93) → `if !all_simple || params.is_empty() { continue; }`
  (drop the `.any(|p| !Scalar)` requirement). Universal: runs for every typed-path language. Step rules
  (Tern/Fact/Pow/cmp/casts) still excluded (gated on `eval_mode == Fold`).
- **§1c** for the genuinely-new **pure-native-arith** folds (all params `Scalar`, output native non-collection),
  bind operands as the NATIVE value, not `&Cat`: `let a = #build(&d)?.try_eval()?;` (the body `a + b` is
  written assuming `a: i32`; the existing `&Cat` binding is for object-param casts and would not compile).
  Keep `let a = &#build(&d)?;` for object-param / mixed folds (byte-for-byte unchanged).
- **§1b** safeify the body for pure-native-arith folds: `safeify_and_wrap(f.body)` (native/rust_code_rewrite.rs:102)
  → `(|| -> Option<_> { Some(<safe>) })()`, then `body_value = ({ #body_ts })?`. Overflow / div-by-zero /
  NaN → `None` → the fold DEFERS (redex unreduced, report still Complete) instead of panicking inside the
  engine closure. MANDATORY (debug overflow panics; `DivInt` by zero panics in both profiles). Keep the
  existing `body_returns_option` path for non-arith folds.
  Add a `FoldRule.is_pure_native_arith` flag (all params Scalar + native non-collection output) computed in
  `collect_fold_rules`; branch on it for §1b/§1c.
- **§1d** widen `needs_typed_fold_path` (dovetail_report.rs:31) so a language whose folds are ALL native-output
  still reaches the typed path: `language.terms.iter().any(|r| r.eval_mode == Some(Fold))`. Narrow fallback
  if a math language regresses: `Fold && (output non-native OR all params Simple/Base)`. Gate by §4-F.

## §2 — Runner: present the normal form (recommendation (a): extract, don't rewrite tests)

`simulation/src/runner.rs` Dovetail arm (479-538). Add `dovetail_extract_normal_form(&report) -> Option<String>`:
- Scan `report.root_ordinals → terms[ordinal]` (funded roots). For a root whose `op_display` is a literal
  variant (`…::NumLit(3)`, `FloatLit(..)`, `RatLit(..)`, …), extract the payload between the outermost
  `(` after `::Ctor` and its `)` → e.g. `"3"`. Pick the first integer-`*Lit` root (deterministic, smallest
  ordinal); all numeric cast alternatives display the same integer value.
- `Some(term)` → `TraceOutcome::NormalForm { term, steps: step_index }` (matches the asserts: 1+2→"3",
  (2+3)*(4-1)→"15", etc.). `None` → keep the existing `RuntimeReport` outcome (free vars / unlowerable).
- Keep the step push + morphology + `NormalFormReachable`-invariant block intact.

## §3 — FV (zero-admission)

`dovetail/formal/rocq/theories/Saturation/DovetailSaturation.v` already proves `saturate_step_sound`
(native rewrites preserve soundness if each generated fact is sound). Add: (1) native-scalar fold reduction
soundness (`dispatch_result = interpreter_eval` under equal reconstructed operands — definitional, since the
same `safeify`'d body + `try_eval` operands as the interpreter), (2) `None`-defer adds no fact (vacuously
sound). Build: `make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail`. No Admitted/Axiom.

## §4 — Regression (exact)

rholang_dovetail_fold (MUST stay 6/6), rholang_dovetail_{op_enum,host_routed}, ambient_dovetail_flip,
ambient_binder_handler, simulation_integration + probe_neg_zero (target → green), gen_calculator_{unit,
rewrite,analytical,prop} + calculator, gen_{basemath,extmath,mixedmath,importedmath,ledtest}_* (§1d guard),
macros, dovetail crate, prattail --lib, simulation, formal rocq-dovetail.
(`dovetail-codegen` now in default; pass `--features rholang` for rholang-cfg'd tests.)

## §5 — Risks

Termination/budget for arithmetic saturation (folds COLLAPSE redices → fewer nodes; confirm nested +
campaign converge); cross-cat cast blow-up (extraction picks one integer literal deterministically);
extraction must actually find `NumLit(3)` (PRIMARY gate — validate codegen fires BEFORE runner edit);
do not regress rholang (object-param casts unchanged; only its pure-scalar `NegInt` newly fires);
`needs_typed_fold_path` broad-widen side effects (math langs — §4-F); try_eval defer for non-literal
children (converges Complete); overflow without safeify (CRITICAL — §1b mandatory).

## §6 — Execution order

1. §1a+§1c+§1b (one coherent typed_report.rs edit). 2. `cargo build -p languages` (fix &Int-vs-i32).
3. Codegen probe: Calculator `1+2` → `NumLit(3)` BEFORE the runner edit. 4. §2 runner. 5. §4-D target tests.
6. §1d decision + §4-F. 7. Full §4. 8. §3 FV + rocq-dovetail.
