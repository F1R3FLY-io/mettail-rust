# E3 — Generalized native-fold-expression → Rholang dataflow execution (design)

> Status: DESIGNED → RED-TEAMED (**NO-GO**, 2 fatal flaws) → **CORRECTED ARCHITECTURE below governs**.
> Companion to `00-design-and-ledger.md` (§E3). The original design (§1–§10, retained as a ledger of what
> failed) is SUPERSEDED by the "Corrected architecture" section; read that section as the authoritative spec.

## Red-team verdict & corrected architecture (AUTHORITATIVE)

The original design (§1–§10) was **NO-GO**: it lowered `dovetail_normal_term(term)`, which is **fatally wrong**.

**FATAL-1 — lower the ORIGINAL term, not the folded NF.** Dovetail's D-stage FOLDS scalar arithmetic
(`is_pure_native_arith`, `typed_report.rs:120,410-413,283`), so the normal form of `(2+3)*(4-1)` is the
literal `15`; lowering it degenerates to `@"OUT"!(15)` — the scalar contracts never fire, defeating the
goal. The F-stage receives the ORIGINAL parsed `term` (`backend.rs:806,1462`), and the existing single-op
`rho_scalar_contract_invocation_to(term,out)` already lowers the ORIGINAL term by downcasting it
(`rho_invocation.rs:402-408`) — never consulting the report. **Fix: walk the original typed AST; use the
Dovetail report only as a completeness gate + Defer-fallback payload.**

**FATAL-2 — `dovetail_normal_term` doesn't exist for pure-scalar-fold languages.** `needs_normal_term`
(`dovetail_report.rs:351-370`) is FALSE for Calculator (all-congruence rewrites, empty equations, no
channels) — the method isn't generated, so the original §10 wrapper wouldn't compile. FATAL-1's fix removes
the dependency (do NOT widen the MF7 gate).

**Corrected architecture (governs implementation):**
1. **Emitter walks the ORIGINAL typed AST.** A new `macros/src/gen/runtime/rho_dataflow.rs` generalizes the
   single-op `rho_invocation.rs` (downcast `<Lang>TermInner`/`<Cat>`, reuse its `literal_extractor` /
   `scalar_literal_variant` arms, `Ambiguous` via `find_map`) from ONE node to a post-order
   `Vec<RhoDataflowNode>`. Per-node ABI via the already-generic `plan_scalar_invocations` keyed by
   `rule_label`. NO `dovetail_normal_term`, NO MF7 dependency.
2. **`rholang-codegen/src/dataflow.rs`** (deps `models`+`ast` only — verified) assembles the closed call
   `Par` via the **multi-bind JOIN** `for(c0<- … & c1<- …){…}` (MED-7: runtime-supported per `PInputs`
   `rholang_ast.rs:391-433`; de-Bruijn-simpler — sources at for-depth 0, one uniform `extend_env` shift),
   with **hard `Result` structural validation** (HIGH-4: closed term / all sources `new`-bound / each `for`
   `free_count==1` / root→`@"OUT"`; `debug_assert!` is compiled out in release). `RhoAstValidationProfile::
   FoldDataflow` is the durable future home (the enum is `#[non_exhaustive]`).
3. **Total Defer gate via generic bottom-up safe-evaluation** (HIGH-3+HIGH-5, parity with Dovetail):
   while walking, constant-fold each node using `checked_*` / safe-arith dispatched on the **operator
   threaded onto the scalar plan** (from `LanguageDef` `SyntaxExpr::Literal`; `rho_binop`/`RhoBinaryOp` are
   module-private so cannot be named). If any node's safe-eval is `None` (`/0`, `%0`, overflow) OR a node is
   non-scalar / non-lowerable / a free var → **Defer the WHOLE term** (a Rho contract would hard-`Err` at
   runtime — `reduce.rs:1677,1752` — where Dovetail's `safe_*` defers; `inj` surfaces it as `Err`,
   `run.rs:294-304`). Defer is total (can't splice a Dovetail subresult onto a Rho channel soundly). The
   safe-eval value is also a **cross-check**: the Rho-observed result must equal it.
4. **3-valued disposition** (MED-6): the emitter returns `Result<RhoFoldDataflowDisposition, String>` where
   `Disposition = Run(RhoFoldDataflowInvocation) | Defer`; `backend.rs` maps `Run → RunWithCallAndObserve
   {Ints,Bools,Strings}` (by root `result_type`), `Defer`, meaning the residual is not fully Rho-lowerable — it fold-normalizes via E2 and runs on
   Rho (the former `Defer → DeferToDovetailReport` mapping was removed; see doc 12). The fictional `Disposition` enum/2-valued return in §10 is dropped.
5. **Single-op = strict subset.** The depth-1 dataflow == `rho_scalar_contract_invocation_to`
   (`run_calculator.rs` proves it); once E3 is verified, route the single-op path through the N-node method to
   remove divergence (do this only AFTER E3 is green — don't destabilize the working single-op path first).

**Retained-correct decisions:** option (a) over the unsound report-walk (b) — the report carries only
`op_display`/`key`, no typed leaf values (`language.rs:300`); the value-level unit-testable `Par` builder;
composition via `par.append` over the existing `RunWithCallAndObserve*` (`run.rs:378`).

**Honest value:** for a closed ground tree E3 is a capability demonstration (Rho differentially re-derives
the safe-eval value) + the on-ramp to channel-borne sub-results; it is the goal explicitly chosen.

---

> The sections below (§1–§10) are the ORIGINAL design, retained as a ledger. Where they conflict with the
> corrected architecture above (notably §10's `dovetail_normal_term`, §5's `debug_assert!`, §6's /0-only
> defer, §3's nested `for`), the corrected architecture wins.

## Goal
Any fold-bearing `language!` language EXECUTES its native-fold expression trees — including NESTED
expressions (`(2+3)*(4-1)`→15, `((10-4)+1)==7`→true, `"a"++"b"++"c"`→"abc") — on the real f1r3node
Rholang `RhoRuntime`, by lowering the expression to a Rholang dataflow of scalar-op contract calls.
"Fully generalized" is a hard requirement: everything derives from `LanguageDef` — NO per-language
hardcoding. (E3 is NOT needed for the Rholang bug or Rholang mixed COMM+fold — that path is E2's
`dovetail_normal_term` + `lower_rholang_term`. E3 is the GENERIC scalar-fold→Rho-contract dataflow.)

## 1. Mechanism decision — a NEW per-language macro emitter (option a)

`macros/src/gen/runtime/rho_dataflow.rs` generates a per-language post-order dataflow lowerer that
downcasts to the concrete `<Lang>TermInner`/`<Cat>` enums. It is the direct generalization of the
existing single-op emitter `macros/src/gen/runtime/rho_invocation.rs` ("one contract call" →
"a nested-`for` dataflow of contract calls").

**Rejected alternatives (on merit, not ease):**
- **(b) generic walk over the Dovetail report — UNSOUND.** `RuntimeDovetailTermRecord`
  (`runtime/src/language.rs:300`) carries only `op_display: String` (a rendered display string, NOT a
  machine rule label), `weight_display: String`, an opaque `key: ExactTermKey` (bytes), `class_id`. It
  carries NO typed leaf literal values (`2`,`true`,`"a"`). Recovering an `i64`/`bool`/`String` leaf or a
  per-node contract label would require PARSING display strings — fragile, precedence/locale-sensitive,
  the exact "source-text-as-boundary" anti-pattern `rholang-codegen` forbids. `derivation_edges` give
  parent→child by key, but with no typed leaf payloads that structure can't be lowered soundly.
- **(c) structural accessor on the `Term` trait — too invasive, wrong long-term shape.** Widens the
  foundational trait every generated language + the whole REPL/runtime implements; forces a new generated
  impl into every `language!` regardless of a Rho backend; and a generic runtime leaf accessor
  re-introduces, at runtime, the type-discrimination `lower.rs`/`invocation.rs` already do CORRECTLY at
  codegen time — inviting divergence. Can't reuse `plan_scalar_invocations`/`check_scalar_arguments`
  without re-deriving operand types at runtime.
- **(a) is most principled:** reuses the already-generic `plan_scalar_invocations(def,&lowering)`
  (`invocation.rs:129`) → per-label `RhoScalarInvocationPlan{abi, operands:[{field_position, category,
  scalar_type}], result_scalar_type}`, derived purely from `LanguageDef` (no display strings). The
  emitter walks the typed AST where the rule label IS the enum constructor (static), children are
  `Arc<Cat>` (recurse), leaf literals are bare native payloads (the same `literal_extractor` pattern
  `rho_invocation.rs:130` emits). No shared-trait widening; soundness inherited from the single-op typing
  checks; generality is structural (constructor + Arc-children), not name-keyed.

## 2. Files
- **NEW `rholang-codegen/src/dataflow.rs`** (runtime-free planner; deps only `models`/ast): value-level
  `RhoDataflowNode{ Internal{abi, operands:Vec<RhoDataflowChild>} }`, `RhoDataflowChild = Leaf(RhoAstLiteral)
  | Node(usize)` (index into a post-order `Vec`); `build_dataflow_call_par(nodes, out_channel) -> Result<Par,
  RhoDataflowError>` (ITERATIVE post-order Par assembler — uses `models::rust::utils`
  `new_new_par`/`new_receive_par`/`new_send_par`/`new_boundvar_par`/`new_freevar_par`/`new_g*_par`, reusing
  the de-Bruijn discipline from `rholang_ast.rs`); `scalar_abi_by_label(lowering) -> BTreeMap<String,
  &RhoScalarContractAbi>`. Par assembler lives HERE (not the macro) because `rho_binop`/`RhoBinaryOp` are
  module-private in `lower.rs` — but the dataflow only emits CALLS to the persistent `@"<Label>"`
  contracts, so it never needs `RhoBinaryOp`; value-level keeps it unit-testable.
- **NEW `macros/src/gen/runtime/rho_dataflow.rs`** (emitter, mirrors `rho_invocation.rs`): emits
  `<Lang>::rho_fold_dataflow_invocation_from_dovetail_to(term, report, out_channel) -> Result<
  RhoFoldDataflowInvocation, String>` behind `#[cfg(feature="rho-codegen")]`. Body: `report.assert_complete()`
  → downcast → generated `__collect_dataflow_<cat>` (explicit-stack post-order over `Arc<Cat>`; `Ambiguous`
  via `find_map` like `rho_invocation.rs:multi_category_try_fn`) building `Vec<RhoDataflowNode>` → any
  non-lowerable constructor / free var / non-scalar / const-zero divisor returns a Defer sentinel →
  `build_dataflow_call_par`. Wire into `mod.rs` + one call at `language.rs:~72`.
- **CHANGE `rholang-runtime/src/backend.rs`**: `build_fold_dataflow_invocation_from_contract(inv) ->
  RhoBackendInvocation` (result-type → `RunWithCallAndObserve{Ints,Bools,Strings}`; mirrors
  `build_scalar_contract_invocation_from_contract:696`). NO change to `RhoBackendInvocation`/`execute`/
  `run_with_call_and_observe_*` (the former `DeferToDovetailReport` intercept has since been removed). The dataflow rides the
  EXISTING `RunWithCallAndObserve*` variants → `evaluate_par(&par.append(call.clone()))` (`run.rs:378`)
  composes the call with the persistent `ScalarContracts` program for free.
- **NO change to `RhoAstValidationProfile`** — emit a bare `call: Par` (§5).

## 3. De-Bruijn discipline (the load-bearing subtlety)
Target `(2+3)*(4-1)` (`@"AddInt"`/`@"SubInt"`/`@"MulInt"` pre-installed):
`new cL, cR in { @"AddInt"!(2,3,*cL) | @"SubInt"!(4,1,*cR) | for(l<-cL){ for(r<-cR){ @"MulInt"!(*l,*r,@"OUT") } } }`
- One fresh name per internal node whose result is consumed by a parent → wrap the whole call in a single
  `new c0,…,c_{k-1} in {…}` (`new_new_par(k, body, …)`); the k result channels are de-Bruijn-bound `0..k-1`.
- Two-layer index arithmetic: a received operand `l`/`r` introduces a `for`-binder that shifts all enclosing
  `new`-bound channel indices up by 1 (`extend_env` `index+width`, `rholang_ast.rs:655`). Received values:
  innermost = `new_boundvar_par(0)`, next-out = `new_boundvar_par(1)` (outward count, matching nested
  `PInputs`).
- Bound vs ground: leaf literals → ground `RhoAstLiteral` directly in the producer send; internal-node
  results → dereferenced received var `*l` inside the consumer `for` body; return channel = own `*c_i`
  (bound, non-root) or `@"OUT"` (ground gstring, root).
- Each `for(x<-c)`: `ReceiveBind{patterns:[new_freevar_par(0,…)], source:chan, remainder:None, free_count:1}`,
  `bind_count:1` (= `rholang_ast.rs:411`). Nesting (one bind each) over a multi-bind join — simpler index
  bookkeeping; join is a deferred optimization.
- `locally_free`: sends via `send_par` union (`:665`); receives via `receive_locally_free` (`:682`) +
  `filter_and_adjust_bitset` (`:690`); outer `new` via `filter_and_adjust_bitset(body.locally_free, k)`
  (`:438`). All channels `new`-bound + all operands ground-or-locally-bound ⇒ top-level `locally_free` EMPTY
  (closed term — required for `inj`).
- ITERATIVE (stack-safety mandate): both `build_dataflow_call_par` and the emitted `__collect_dataflow_<cat>`
  use explicit work-stacks (no native recursion over tree depth), as `language.rs:306`/`normalize_iterative`.

## 4. Generic derivation from `LanguageDef`
- Per-node contract label = the typed enum CONSTRUCTOR name (`enums.rs:generate_variant` uses `rule.label`);
  known statically at codegen (no runtime lookup). ABI via `plan_scalar_invocations` keyed into a
  `BTreeMap<String,RhoScalarInvocationPlan>`.
- Per-operand category + scalar type from `RhoScalarInvocationPlan.operands[i].{category, scalar_type}`
  (`invocation.rs:183`).
- Leaf values via the exact `literal_extractor` arms (`rho_invocation.rs:130-176`): `#cat::#lit(v) =>
  Int(i64::from(*v))|Bool(*v)|String(v.clone())`; leaf label via `scalar_literal_variant`
  (`rho_invocation.rs:107`). Both label and value derive from `LanguageDef` + the macro-expanded enum, never
  from display/`op_display`.

## 5. Validation — bare `call: Par`, NOT `CallByNeedThunk`, NOT a new profile (yet)
`CallByNeedThunk`'s validator hard-codes a 5-channel `bind_count==5` thunk topology — would reject a generic
dataflow (user mandated: don't reuse it). The single-op precedent already ships the bare-call path
(`build_scalar_contract_invocation:668` returns `RunWithCallAndObserve*` with no `ValidatedRhoProgram`; the
call composes at run time via `par.append`). In-builder `debug_assert!`/`Result` structural checks (closed
term, all sources `new`-bound, each `for` `free_count==1`, root → `@"OUT"`) replace a global profile. A
`FoldDataflow` profile is the designated future extension point (`RhoAstValidationProfile` is
`#[non_exhaustive]`).

## 6. `/0`,`%0` / non-scalar / free-var → `Defer` (MF6)
The Rho contract path is unguarded for `/`,`%` (→`EDiv`/`EMod`, no zero check). Three decidable Defer classes
in the collector, BEFORE building any node:
1. constant-zero divisor (right operand collects to `Leaf(Int(0))` for a `/`/`%`-terminal rule);
2. non-scalar/Big/Float/collection/cast/ternary/etc. (label ∉ the `plan_scalar_invocations` lowerable set);
3. free vars / non-ground leaves (a `Var` leaf the `literal_extractor` rejects).
Defer is TOTAL (a Defer at ANY node Defers the whole term — can't soundly splice a Dovetail subresult as a
Rho channel value). Maps to `RhoFoldDataflowDisposition::Defer` (the former `DeferToDovetailReport`
intercept was removed — see doc 12). This is the "every op runs somewhere" semantics — flat/all-scalar
trees run fully on Rho; a tree containing a non-Rho-lowerable op Defers wholesale, and the outer F-stage
then fold-normalizes it (E2) and runs it on Rho. NOT the rejected flat-op-only shortcut.

## 7. Soundness + generality
- Per-op = the existing M-RHO differential oracle (`@"<Label>"` contract ≡ the scalar rule, checked by the
  oracle / `RhoLoweringTotalOrRejects.v`). E3 adds NO operator semantics — it COMPOSES proven contracts.
- Composition: single-assignment channels; each internal node publishes its unique result on a fresh
  `new`-bound channel; the parent `for` consumes that one value. Evaluation order is enforced by DATA
  DEPENDENCIES (`for(l<-cL)` can't fire until `@"AddInt"!(…,*cL)` produced) ⇒ the observed `@"OUT"` value =
  the term's denotation, regardless of interleaving (each channel carries exactly one datum; leaf producers
  commute). Matches the `RhoObservationReport` membership-fingerprint contract.
- Generality: keys on STRUCTURE (constructor=label, `Arc<Cat>`=child, native payload=leaf) + the
  `LanguageDef`-derived `plan_scalar_invocations`. Nothing references "Calculator"/"AddInt".

## 8. Edge cases
- Already-constant-folded NF (single literal): collector yields one `Leaf`; emit trivial `@"OUT"!(v)` (no
  `new`/`for`). Common case post-E1/E2.
- Unary (`not a`,`-a`): one-operand node (`UnaryPrefix`).
- Bool/Str roots → `RunWithCallAndObserveBools/Strings`.
- Ambiguous parses: `find_map` over alts (safety net; NF path usually single).
- Deep trees: iterative (§3).
- Mixed lowerable/non-lowerable: Defer wholesale (§6).

## 9. Verification plan
- Unit (`dataflow.rs`, runtime-free): `build_dataflow_call_par` for `(2+3)*(4-1)` → exactly one top-level
  `new` (bind_count 2), two producer sends on bound channels, nested `for`s `free_count==1`, root send to
  ground `@"OUT"`, empty top-level `locally_free`.
- Integration (a fold-bearing language with a Rho backend; on the real in-memory `RhoRuntime`): `(2+3)*(4-1)`
  →Int 15; `((10-4)+1)==7`→Bool true; `"a"++"b"++"c"`→Str "abc"; 64-deep chain (no stack overflow);
  already-folded→trivial; Defer cases (BigInt; `int(1/0,8)` const-zero — confirm no `EDiv` reaches the
  runtime; free-var; mixed tree) → assert the wrapper returns a DOVETAIL report (never an error, never a Rho
  run); generality via a SYNTHETIC renamed-scalar language (mirrors `invocation.rs` renamed-native test +
  the `lambda_dovetail_synthetic.rs` precedent).

## 10. Sequencing + downstream
Order: (1) `dataflow.rs` planner + unit tests (standalone); (2) `backend.rs` adapter; (3)
`rho_dataflow.rs` emitter + wiring; (4) downstream Calculator two-stage wrapper `F` — the ONLY per-language
glue, uniform across fold langs:
```
|term, report| {
    report.assert_complete()?;
    let nf = <Lang>Language::dovetail_normal_term(term, MAX_ITERS, MAX_NODES)?;   // E2.2
    match <Lang>Language::rho_fold_dataflow_invocation_from_dovetail_to(nf.as_ref(), report, OUT)? {
        Disposition::Defer    => /* fall back to E2 fold-normal, run on Rho; DeferToDovetailReport removed (doc 12) */
        Disposition::Run(inv) => build_fold_dataflow_invocation_from_contract(inv).map_err(|e| e.to_string()),
    }
}
```
The single-op `rho_scalar_contract_invocation_from_dovetail_to` becomes a strict subset (depth-1 tree);
recommend routing all fold terms through the dataflow method to avoid two divergent paths.
