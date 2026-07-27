# Generalized Dovetail/Rho Macro-Codegen Extensions — Design & Progress Ledger

Last updated: 2026-06-23

> **STATUS: COMPLETE ✅** — All three macro extensions (E2 → E1 → E3) and the downstream REPL wiring
> are implemented, verified, and committed; `exec` now works for every bundled language with
> capability-based backends. Commits: **E2** `6a8cc0ad`; **E1** `e463895c`; **E3** `90b59dfa`
> (planner) + `e17fba8e` (emitter+runtime) + `26e50fe2` (walk); **AppSubst fixture** `c0166564`;
> **downstream** `cdc81c89`. Verified: `dataflow` unit 6/6 · `run_dataflow` (real RhoRuntime) 5/5
> (`(2+3)*(4-1)`→15, `==`→true, `++`→"abc", literal, deep chain) · `rho_dataflow_walk` 2/2 ·
> `lambda_dovetail` 6/6 · `lambda_dovetail_synthetic` 3/3 · `dovetail_normal_term` 4/4 ·
> `rho_rholang_ast` 17/0 · `registry_exec` 2/2 · macros lib 221 · `gen_appsubst_*` 73/0 · **manual REPL
> session 6/6** (pure-COMM→`OUT:[p]`, mixed `@("OUT")!(int(1+2,8))`→`OUT:[3]`, `int(1+2,8)`→Dovetail,
> `1+2`→`OUT:[3]`, `(2+3)*(4-1)`→`OUT:[15]`, `(lam x.x, y)`→`y`). E3's authoritative spec (with the
> red-team NO-GO→corrected architecture) is `01-e3-dataflow-design.md`.

## Context

The `mettail` REPL `exec` failed for all bundled languages because raw `language!`-generated
languages advertise no runtime backend (root cause + the registration fix are in
`~/.claude/plans/which-end-to-end-integration-tests-composed-milner.md`). Wiring the runtime-backed
wrappers surfaced three deeper, **empirically verified** gaps (two probe runs, ground truth):

1. **Lambda has no working Dovetail backend.** `LambdaLanguage::dovetail_report_for` errors:
   *"rewrite `Beta` RHS: multi-substitution patterns require generated substitution lowering."* Its
   `normalize_term` does not β-reduce, and its `rewrite_seeds` carry no `exact_key`. Lambda has had
   no reducer since Ascent was retired.
2. **e-graph→AST reconstruction skips `Collection`/`Binder`/`MultiBinder`** (`reconstruct.rs:89-91`
   → `None`), so a Dovetail normal form containing `PPar`/`PInputs`/`PNew` cannot be recovered as a
   typed term — blocking mixed-term (COMM-with-fold) Rho execution.
3. **No general expression→Rho lowering.** Only single scalar ops lower to Rho contracts
   (`run_calculator.rs`); nested expressions have no dataflow lowering.

The user directed: fix all three **fully generalized** (derived from `LanguageDef`, no per-language
hardcoding), designed by a Plan agent and **red-teamed**. The red-team returned NO-GO until 7
must-fixes (MF1–MF7), all integrated below. Order is **E2 → E1 → E3** (E1's β-dispatch needs E2's
binder reconstruction; E3 needs E2's `dovetail_normal_term`).

## Verified ground-truth anchors
- Typed path: `dovetail_report.rs:31` `needs_typed_fold_path`; `:576` early-returns to
  `typed_report.rs:444`. Uses `EGraph<L>` + `saturate_with_native` (`:554`) + generated `NativeRule`s
  /dispatcher (`:250`) + reconstruction. String path (`:726` `eg.saturate`) has **no** native dispatch.
- Substitution primitive: `(*body).substitute_<dom>(&binder.0,&arg)` after `scope.unbind()`
  (`normalize.rs:2091`); iterative `subst_iterative` (`subst.rs`); oracle `lambda-datalog.rs:118`.
- `(eval f a)` parses to `MultiSubst{scope:Var(f),replacements:[Var(a)]}` (`parse.rs:2641-2701`);
  rejected at `dovetail_report.rs:441`.
- AC-bag multiplicity **is** carried (`HashBag::iter_elements` flat-maps `repeat_n(k,count)`,
  `hashbag.rs:269`; `typed_lowering.rs:57`). Binder identity erased = FIX-A `BinderArity(n)`
  (`typed_lowering.rs:165`); body keeps positional de-Bruijn `BoundVar`.
- The former `RhoBackendInvocation::DeferToDovetailReport` catch-all has since been REMOVED —
  superseded by `DeferToDovetailSemanticPredicate` (semantic-predicate blocks) plus
  `RhoFoldDataflowDisposition::Defer` for non-Rho-lowerable folds (`dataflow.rs:103`); folds otherwise
  fold-normalize (E2) and run on Rho (see doc 12 + rho-native-integration doc 09).
- AC-collection metapattern LHS rejected on typed path (`dovetail_report.rs:415-420`) → Rholang
  `Comm` stays inert.

---

## E2 — Reconstruction inverse + `dovetail_normal_term` (FIRST)

**E2.1 — `reconstruct.rs`:** add `Collection`/`Binder`/`MultiBinder` arms as the exact inverse of
`typed_lowering.rs` (`category_lowering_typed` `:122`; binder `:146`; AC bag `:57/214`):
- **Collection (AC bag):** push a child per `d.children[i]` (multiplicity carried), rebuild via the
  generated `Cat::insert_into_<label>` flatten helper (`normalize.rs:117`) — restores multiplicity
  faithfully (MF3; do **not** fail-closed on multiplicity>1). Only `HashBag` invertible; `Vec`/`Set`/
  `Map` lower to `FieldOpaque` → stay `None`.
- **Binder:** children `[…pre, BinderArity(1), body]`; rebuild `Scope::from_parts_unsafe(fresh_binder,
  Arc::new(body))` (`normalize.rs:1853`) with a **fresh** binder; body's positional de-Bruijn coords
  stay valid ⇒ result ≡α original (correct; NFs are α-classes).
- **MultiBinder:** `BinderArity(n)`; n fresh binders (`normalize.rs:1884`); assert arity.
- **MF3/NEW#6 (stack safety):** prefer an iterative work-stack driver mirroring `normalize.rs`'s
  `normalize_iterative` over the naive recursive `build_fn`. (Decision recorded in ledger: start
  iterative; if the iterative macro proves too risky in one step, land recursive arms — consistent
  with the *existing* recursive `build_fn`+extractor — and harden iteratively as a follow-up, since
  this introduces no new recursion class.)
- Round-trip law to preserve: `build_<cat>_d(lower(t)) ≡α t`.

**E2.2 — `typed_report.rs`: emit `dovetail_normal_term(term,max_iters,max_nodes)->Result<Box<dyn Term>,String>`**
beside `dovetail_report_for` (`:444`). Same saturation prologue; per root (or `all_alts()` →
`TermInner::Ambiguous`) `funded_best` → `build_<primary>_d` → wrap in `<Lang>TermInner`/`<Lang>Term`.
Fail-closed `Err` on `None`/`BoundedByCycleCut`/non-`Converged`.
- **MF7 gating:** emit only when `needs_normal_term(language)` = has-substitution-rewrite ∨
  has-typed-path-structural-rewrite ∨ declares-Rho-backend; optionally also `#[cfg(feature =
  "dovetail-normal-term")]` to bound compile-time on the heavy `languages` crate.

---

## E1 — Generalized substitution lowering (SECOND; needs E2 binder reconstruction)

**E1.1 routing:** `dovetail_report.rs:31` `needs_typed_fold_path` → `needs_typed_dovetail_path` =
`has_native_fold ∨ rewrites.any(is_substitution_rewrite)`. Routes β-languages to the typed path.

**E1.2 detector (MF4, shape-guarded):** `is_substitution_rewrite(rw)->Option<SubstRewrite>` accepts
ONLY: RHS is exactly `MultiSubst{scope:Var, replacements:[Var|plain-ground-term]}` (or single
`Subst`), single binder, replacements not Map/Zip/Collection, RHS not nested in AcApp/Collection/
Apply, LHS not AC-collection-nested, premises congruence-only, scope_var bound by a Binder/MultiBinder
in LHS. **Verifies Rholang `Comm` is NOT detected** (its replacement is a `Map`, nested in AC `PPar`).
`SubstRewrite` carries label, LHS pattern, scope_var, repl_vars, and (from the matched
`VariantKind::Binder`) `binder_label`/`binder_cat`/`body_cat`.

**E1.3 op_id (MF2):** substitution `NativeRule` op_ids start at `folds.len()`; own dispatch arms;
shared counter across folds ∪ substitution rules; do not route through `collect_fold_rules`.

**E1.4 dispatch arm (MF5):** in the dropped-`Extractor`-scope-then-mutate discipline
(`typed_report.rs:321`): gate scope+repl classes on `__class_is_fold_value`; `kth(...,0)` the child
derivations; `build_<binder_cat>_d` (E2) the binder term + `build_<repl_cat>_d` the replacement;
`let Cat::<binder_label>(scope) = … else return None`; `scope.unbind()`; `substitute_<binder_cat_lc>`
(or `multi_substitute_…` with arity assert); re-add via `__mettail_dovetail_add_<body_cat>`. Own
`body_value` handling (not `is_pure_native_arith`, no `safeify`).

**E1.5 progress weights (MF1, FATAL — land atomically with E1.4):** extend `generate_helpers`
(`typed_report.rs:185`) so the redex-head set = fold heads ∪ substitution-rewrite LHS head ops:
`__is_redex` (was `__is_fold_redex` :224), `__is_value_op` (:229) excludes β-redex heads, `__weigh`
(:234) gives β-redex 100.0, `__class_is_fold_value` (:240) no longer treats an un-reduced `App` as a
value. Without this β fires but extraction never selects the contractum.

**E1 divergence (MF5):** non-normalizing β (Ω) exhausts `__iters`/node budget → non-`Converged` →
`Err` (`typed_report.rs:555`); `struct_slack` over-estimate cannot mask divergence.

---

## E3 — Generalized expression→Rho dataflow (THIRD; needs E2 `dovetail_normal_term`)

**Scope:** exact for the scalar-Rho-representable fold subset (`lower.rs::rho_binop`/`rho_unop`
`:353/:386`, Int/Bool/Str); grammar-derived, not Calculator-specific; everything else fail-closed.

**E3.2 (`rholang-codegen/src/dataflow.rs`, net-new):** `lower_fold_expr_to_dataflow(def,lowering,
expr,out_channel)`. Op-variant ↔ `RhoScalarContractAbi` by rule label (`lower.rs:530/255`, a
by-index `Vec`, labels unique). Iterative post-order (work-stack): fresh channel per internal node
(`new_new_par`); leaf literals are their own value channel; internal op joins operand channels then
sends `@"<Label>"(v1..vn,ret)` (`RhoAstSend::contract_call`, `ast.rs:269`); root → `out_channel`.
Validate under `RhoAstValidationProfile::CallByNeedThunk` (`lower.rs:131`). Result invocation =
`RunWithCallAndObserve{Ints,Bools,Strings}` by root `RhoScalarType` (`backend.rs:679`).

**E3.3 `/0`,`%0` (MF6):** scalar path maps `/`→`EDiv`,`%`→`EMod` unguarded (`lower.rs:370`); Dovetail
defers via `safe_div` (`typed_report.rs:392`). E3 **rejects** a residual constant-zero-divisor op
(and free-var/non-scalar/Big/Float/collection ops) → `RhoFoldDataflowDisposition::Defer` (not fully
Rho-lowerable; the residual falls back to the E2 fold-normal path, run on Rho) rather than emitting raw
Rholang `EDiv`/`EMod`.

**E3.4 wrapper:** `DovetailRhoRuntimeBackedLanguage` invocation compiler `F` (`backend.rs:1386/1462`)
for fold-bearing langs: `dovetail_normal_term` → `lower_fold_expr_to_dataflow` on the residual →
`RunWithCallAndObserve*` or `RhoFoldDataflowDisposition::Defer`. Fingerprint/install path unchanged. Rholang
structural `Proc` lowering (`rholang_ast.rs`) stays hand-written (generalizing *structural process*
lowering is out of scope).

---

## Verification (per extension)
- **E2:** `dovetail_normal_term` on `@("OUT")!(int(1+2,8))`→`@("OUT")!(3)`; `{ @("OUT")!(int(1+2,8)) }`
  (PPar); `{ int(1,8) | int(1,8) }` (multiplicity 2); a `PNew`/`PInputs` term (≡α); a `Vec`-field NF → `Err`.
- **E1:** Lambda `(lam x. x, y)`→`Complete`/`y`; `(lam x.(x,x), w)`→`(w,w)` (MF1); nested; Ω→`Err`
  (MF5); **MF4 negative:** Rholang `Comm` not detected; synthetic `AppSubst` + cross-cat `[Name->Proc]`
  binder languages reduce (generality).
- **E3:** `(2+3)*(4-1)`→`15` on RhoRuntime; `((10-4)+1)==7`→`true`; `"a"++"b"++"c"`→`"abc"`; BigInt →
  `Defer`; `int(1/0,8)` → `Defer` (MF6).

## Progress ledger
- [x] Design (Plan agent) + red-team (NO-GO/7 must-fixes) + converge (this doc).
- [x] `dovetail_backed` generic helper (`dovetail-runtime/src/lib.rs`) — compiles (`cargo check` green).
- [x] **E2.1** reconstruct Collection/Binder/MultiBinder arms (recursive, consistent with existing
  `build_fn`; `#[allow(unreachable_patterns)]` on the defensive catch-all). Multiplicity preserved;
  binders α-faithful (fresh binder, positional de-Bruijn). Iterative-hardening = noted follow-up.
- [x] **E2.2** `dovetail_normal_term` + `needs_normal_term` gating (substitution ∨ typed-structural
  ∨ Rho-backend). Verified: `languages/tests/dovetail_normal_term.rs` 4/4 (PPar collection,
  multiplicity-2, fold-in-POutput, PNew α-equiv); rholang_dovetail_fold 6/6, ambient_dovetail_flip 3/3.
  NOTE: a pre-existing `unreachable_patterns` warning in `rho_scalar_invocation.rs` (MixedMath, NOT E2)
  to be fixed during E3.
- [x] **E1.1–E1.5** routing (`needs_typed_dovetail_path`), shape-guarded detector
  (`is_substitution_rewrite` — Rholang `Comm` double-rejected via Map-replacement + AC-LHS guards),
  op_id after `folds.len()` (MF2), dispatch arm (MF5: build→unbind→`substitute_<cat>`→re-add), and
  progress weights (MF1: redex-head set = folds ∪ subst LHS heads). Verified: `lambda_dovetail.rs`
  6/6 (incl. Ω fixed-point, gate-4 corrected — round-trip is unsound for bound-var bodies under
  fresh-binder `_` rendering), `lambda_dovetail_synthetic.rs` 3/3 (synthetic `AppSubst` β-reduces ⇒
  generality proven, not Lambda-name-keyed). No regressions (rholang_dovetail_fold/host_routed,
  ambient_dovetail_flip, dovetail_normal_term, macros lib 221). NOTE: `_`-unnamed-binder rendering
  is α-correct but lossy on re-parse (display polish; tracked as a refinement, not a soundness issue).
- [ ] **E3.2–E3.4** dataflow lowering, `/0` policy, wrapper wiring.
- [ ] Downstream: 4-language registry wrappers + REPL `rho-languages` Cargo wiring.
- [ ] Tests: E2/E1/E3 probes promoted to real tests; `repl/tests/registry_exec.rs`; remove `zz_probe_*`.
- [ ] Full build + workspace tests + manual REPL session (plan verification table).

## Scratch probes (remove before final)
`languages/tests/zz_probe_rholang_fold_normalize.rs`, `languages/tests/zz_probe_dovetail_backends.rs`
— investigation aids; keep until E1/E2 verified, then delete.
