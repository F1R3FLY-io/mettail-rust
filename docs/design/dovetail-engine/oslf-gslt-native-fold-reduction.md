# Dovetail as the Foundational OSLF/GSLT Rewrite Engine — Native Fold Reduction

**Status:** design + staged implementation (2026-06-17).
**Branch:** `feature/wfst-architecture`.
**Supersedes:** the recursive-`try_direct_eval` fold approach (red-teamed + rejected) and the
reify-map Dovetail variant (red-teamed + rejected as unsound).

## 0. Mandate and framing

Dovetail is, by intended design, **the substrate-neutral rewrite engine for MeTTaIL
semantics** (epic `dovetail-gslt-reduction-engine-f1r3node-target`, #278). This document
makes that role total for the **fold fragment** of the operational semantics, which the
Ascent retirement (P6) exposed as the one reduction class still living outside Dovetail.

Two specifications govern it:

- **GSLT** — *Generalized Syntax/Law Theory*: a language definition = **syntax + equations +
  rewrites + operational laws** (`LanguageDef`). Dovetail's saturation **is** the GSLT
  reduction relation: it closes a term under the equations, rewrites, congruence, and AC of
  the theory.
- **OSLF** — *Ordered Linear-Substructural Funding*: the cost/resource discipline
  `is_funded(Δ, Σ, margin) = Δ + margin ≤ Σ` with the four laws (sound, reject-underfunded,
  supply-monotone, decidable), delegated to the verified `delta_sigma`
  (`MettaOslfLawsConformance.v`, `LinearLogicResources.v`). Dovetail's **weight algebra
  (`rigail` semirings) + node/iteration budgets + lazy demand-driven best-first extraction**
  *are* OSLF funding realized: **weight orders, never prunes** (no contraction — the
  substructural law), exploration is funded by weight and bounded by budget, and
  `RhoCallByNeedBudget.v` already proves the force/heap accounting.

**Therefore a fold is an OSLF-funded GSLT rewrite.** It must reduce *inside* Dovetail's
funded saturation like every other rewrite — not on a private, unfunded side-path. The
recursive-method approach (a generated `try_fold_to_self` reached via `try_direct_eval`)
was rejected precisely because it is such a side-path: a second reduction semantics outside
the foundational engine, contradicting Dovetail's design and its architectural position
(macro lowers GSLT→Dovetail; Dovetail saturates under OSLF funding; the Rho backend lowers
Dovetail semantics → Rholang/RSpace; reports/flip-gate/REPL are report-native over Dovetail).

## 1. The problem, exactly

`fold` rules whose **output category is non-native** (RhoCalc/Calculator `Proc`: the numeric
casts `int/uint/float/fixed/bigint/bigrat`, the arithmetic/comparison/collection ops, etc.)
have a `![{ … }]` Rust body (`numeric_dispatch.rs::rho_proc_*`/`calc_*`). That body was
emitted **only** into Ascent's `fold_proc` relation (stale spill
`target/generated/rhocalc/rhocalc-datalog.rs:5161-5746`). P6 removed Ascent ⇒ the bodies are
dead and these casts reduce nowhere. The generated Dovetail report compiler
(`macros/src/gen/runtime/dovetail_report.rs`) lowers only `equations` + `rewrites` into the
e-graph; it never sees folds, and `try_direct_eval` is empty for a non-native primary type.

Ground truth of the fold relation (to replicate faithfully):
- **Base case:** a literal / already-`Cast*` / structural `Proc` folds to **itself**.
- **Recursive redex:** `fold_proc(IntBinProc(l,w)) <-- fold_proc(l, lv), fold_int(w, rv), …
  rho_proc_int_bin(&lv, rv)` — **each child is folded first** (premise gating), the bound
  children are **folded typed terms**, then the body runs; a var/stuck child ⇒ the premise
  has no solution ⇒ **no fold**.
- **Termination invariant:** a fold result is always a `Cast*` literal, which carries **no
  fold body**, so a fold output can never re-match a fold LHS — no unbounded tower. (Held for
  the current grammar; generalized below via the OSLF node budget.)

## 2. Architecture: native-computed GSLT rewrites in the typed e-graph

### 2.1 Typed `L` (the substrate)

The production e-graph today is `EGraph<String>` (op labels like `"RhoCalc::Proc::IntBinProc"`;
literal leaves via lossy `{:?}` Debug). To run a *typed* fold body inside saturation you need
typed children. The principled, lossless realization — and the only one the red-team did not
refute — is to let the e-graph carry a **generated typed op-enum** `L` per language:

```rust
enum ProcOp { IntBinProc, NumLit(i64), CastInt, … }   // literals carry their payload
```

`EGraph<L>`/`RewriteRule<L>`/`Extractor` require only `L: Clone + Eq + Hash + SemanticHash`
(`+ Display` for the runtime projection); the engine and the
NBest/Enumeration/InsideWeight proofs are **generic over `L`** (every `op.as_str()` is
`#[cfg(test)]`), so the engine layer is untouched — the cost is concentrated in the codegen
lowering + the runtime report projection (and the report-key bytes it stamps). With literals
in the node, **reconstruction is total and lossless** — no reify map, no Debug round-trip,
no `EClassId`-keyed side table (the red-team showed the reify map is unsound under `merge`).

### 2.2 Native-computed RHS (the engine mechanism), rules-stay-DATA

`RewriteRule.rhs: Pattern<L>` becomes:

```rust
pub enum Rhs<L> { Pattern(Pattern<L>), Native(NativeOpId) }   // NativeOpId = u32 tag
```

A `Native` rule names, by **tag**, a generated native transition; `saturate` is given a
**dispatcher** `&dyn Fn(NativeOpId, &mut EGraph<L>, &Subst) -> Option<EClassId>`. This keeps
`RewriteRule` plain-old-data (`Clone + Debug`, serializable, inspectable — honoring the
"rules are DATA" doctrine, rules.rs:3); the single compiled-in escape is one generated
dispatcher per language. (Rejected: `Rhs::Native(Arc<dyn Fn>)` — closures-in-data break the
doctrine + the `Debug` derive.)

`saturate`'s per-match branch: for a `Native` rule, call `dispatch(tag, eg, subst)`; on
`Some(result_class)` and `find(root) != find(result)`, `merge`. The dispatcher arm:
1. reads each LHS-var child class from `subst`;
2. extracts the **funded 1-best** typed child (`best_derivation`, the same admissible
   inside-weight the report uses) — this is where OSLF funding selects the child;
3. reconstructs typed children directly (typed `L` ⇒ trivial);
4. runs the user fold body (`rho_proc_int_bin(&a, w)`) — **reviving the dead helpers**;
5. `add`s the typed result back and returns its class.

A var/stuck child has no reducible derivation the body accepts ⇒ the body's `?`/`None` path
⇒ no merge (faithful to premise-gating). A genuine bad cast yields `Proc::Err` (a legitimate
fold value, merged — faithful to Ascent).

### 2.3 OSLF funding on the rewrite (the alignment)

A native fold is a **funded transition**: its weight is a first-class `rigail` cost, and the
node budget (`EGraphConfig::max_nodes`) is the OSLF supply Σ — saturation refuses a fold that
would exceed it (`node_limit_reached` ⇒ `NodeLimit`), exactly `is_funded(Δ,Σ,margin)`. This
generalizes the termination invariant: even if a future grammar had a re-matchable fold
output, the OSLF budget bounds it (funded ⇒ bounded), so saturation always reaches
`Converged`/`NodeLimit` — no unfunded infinite tower.

### 2.4 Progress weight (red-team blocker, essential)

The report extracts under uniform-zero weight today (`dovetail_report.rs`), so the redex and
its folded value tie and extraction could surface the **unreduced** redex. The weigher must
make a native-fold result (a `Cast*` literal) **strictly cheaper** than its redex, so the
funded 1-best extraction surfaces the reduced normal form. (This *is* OSLF funding choosing
the lower-cost derivation.)

### 2.5 Report wiring

`complete_native_dovetail_report_for_language` must become **non-fatal**: a `Proc` fold now
reduces through `eg.saturate(rules, dispatch, …)` + extraction, not through the empty
`try_direct_eval`; `DirectEvaluationUnavailable` falls through to saturation rather than
erroring. Host-routed COMM/`new`/`PZero` carry no fold body ⇒ no fold LHS matches them ⇒
they stay unreduced (`rhocalc_dovetail_host_routed.rs` stays green).

## 3. Formal bridge (zero-admission)

- `GeneratedReportCompiler.v`: a **fourth disposition** `NativeFoldLowered` (a native RHS is
  not a `Pattern→Pattern` rewrite), with requirement `ReqExactContentKey` (the result is
  added through the exact-key path) and the classification theorems extended (total
  `destruct` closes the new case by `reflexivity`).
- An explicit **native-function soundness axiom**: `rho_proc_int_bin(a,w)` *is* the GSLT value
  of `int(a,w)`. This is the same trust boundary native eval already lives behind, now named
  honestly rather than hidden — it is the ONE place the hand-written numeric Rust is trusted.
- `DovetailSaturation.v`: the native equality is a `good` generated fact, so
  `saturate_step_sound`/`_monotone` extend with the soundness hypothesis made explicit;
  `native_refire_is_noop` (a re-fired fold merges nothing). **OSLF funding bridge:** the
  funded-transition cost composes with the existing `RhoCallByNeedBudget.v`/`delta_sigma`
  funding laws — a fold step is funded iff `Δ_fold + margin ≤ Σ`.
- **Unaffected (provenance-blind over `L`):** `NBestExtraction.v`, `EnumerationCompleteness.v`,
  `InsideWeightSccClosure.v` — they take the node set as given.

## 4. Implementation increments (each green + committed)

1. **Engine native-RHS + funding hook** (`dovetail/src/rules.rs`, `egraph.rs`): the `Rhs`
   enum, the `NativeOpId` tag, the `saturate` dispatcher param, `best_derivation`, and the
   progress weight. Additive — existing `Pattern` rewrites unchanged. Unit test: a synthetic
   native rule (`double(n) -> 2n`) fires, merges, converges, and is funded by the budget.
2. **Typed `L` codegen** (`dovetail_report.rs`): generate the per-language typed op-enum +
   its `SemanticHash`/`Display`; migrate the lowering + report projection off String labels.
3. **`lower_fold`**: emit each non-native-output fold as a `Native` rule + a dispatcher arm
   calling the typed body; non-fatal native gate. Revives `rho_*`/`calc_*`.
4. **OSLF funding** wired as the fold-transition weight + the budget-as-Σ bridge.
5. **Rocq:** `NativeFoldLowered` disposition + native-soundness axiom + saturation/funding
   bridge.
6. **Tests:** `int(7,64)`; nested `int(1+2,8)` (funded saturation recursion); var
   `int(x,8)`→no-reduce; bad cast→`Err`; `"0"`→no-reduce (host guard); Calculator `at`/`get`;
   `Converged`; extraction surfaces the folded form; **0 dead-code** (`rg 'never used.*rho_'`).

## 5. Rejected alternatives (for the record)

- **A — recursive `try_fold_to_self` method:** a reduction path *outside* Dovetail; not
  OSLF-funded, not a GSLT-rewrite-in-the-engine; contradicts Dovetail's foundational role.
- **B — Dovetail + reify-map:** UNSOUND — `merge` conflates redex+value in one class so
  `reify[find(class)]` is ambiguous, and the ContentKey tiebreak is unstable across `rebuild`.
- These were the red-team's findings; C (typed-`L`) is the principled survivor and the one
  that realizes "Dovetail is the foundational OSLF/GSLT rewrite engine."
