# V4 — Ambient Binder + Freshness (CONVERGED: sound, alpha-canonical, bounded-honest, disposition-first)

> Lineage: v1 (in-engine de-Bruijn) REFUTED `→` v2 (db/fv split + guard) REFUTED `→` v3 (moniker native
> handler) Part A VERIFIED, composition REFUTED `→` v4 = v3 + five round-3 fixes.
> Sources: `/tmp/b0/ambient-binder-redteam-round{1,2-convergent,3-findings}.md`, `…design-v3.md`.

## 0. Architecture (CONVERGED, Part A verified airtight)
Ambient's six binder equations are DETERMINISTIC congruences `⇒` by the campaign's disposition-first rule
(in-engine iff ambiguous AND host-less) they are NOT in-engine — they are a **moniker-based NativeHandler**
disposition. The handler uses moniker's capture-safe primitives (`unbind` freshen+open → structural move →
`Scope::new` re-close, which recomputes de-Bruijn coordinates LOCALLY). The genuinely-ambiguous AC
reduction (InRule/OutRule/OpenRule) stays in-engine (P4, done). `run_ascent` itself is capture-unsound on
these equations (VERIFIED: `from_parts_unsafe`+`normalize`, no re-close), so the moniker handler is the
GOLD reference; differential-vs-Ascent is valid only on the non-capturing corpus + a negative pin.

## 1. The five fixes (v4 = v3 + these)

### FIX-A (gating) — alpha-canonical binder identity (closes #3, #4-dedup, #5-idempotence)
ROOT CAUSE: moniker `unique_id` (process-global counter, freshened by every `unbind`, never reset) leaks
into binder identity at three sites, making `exact_key`/`content_key` run-varying.
CHANGE binder hashing/comparison to be ALPHA-CANONICAL — hash/compare the de-Bruijn BODY (already
alpha-canonical) + binder ARITY, EXCLUDING the binder's `FreeVar` identity:
- (c) `semantic_hash` PNew arm (generated; macro `macros/src/gen/runtime/semantic_hash.rs` or wherever the
  PNew arm is emitted → `target/generated/ambient/semantic_hash.rs:51-58`): replace
  `Hash::hash(&f0.inner().unsafe_pattern, state)` with hashing the arity + recursing into the de-Bruijn
  `unsafe_body` only. Two alpha-equal `new`-terms then hash equal (matches `term_eq`).
- (d) e-graph binder label (generated; `macros/src/gen/runtime/dovetail_report.rs binder_arm:198-249` →
  `target/generated/ambient/dovetail_report.rs:111-128`): replace
  `format!("{}::{:?}", binder_label, scope.unsafe_pattern())` with an arity-only anonymous marker
  `format!("{}::arity::{}", binder_label, n)`; the body child already carries de-Bruijn coordinates.
- (a) `Scope::cmp`/Ord + `OrdVar::cmp` (runtime `binding.rs:230-252,411-421`): compare the de-Bruijn body
  (+ arity), not the binder's FreeVar hash. Makes the NewComm float-prefix sort run-stable.
WHY SAFE: aligns identity with moniker `term_eq` (which already ignores binder names); only Ambient
exercises binder hashing today (Calculator: no binders; rhocalc: binders`→`host) `⇒` no flipped-lang
regression. This is a genuine correctness fix (binder hashing currently OVER-distinguishes alpha-variants).
RUST: bound occurrences stay de-Bruijn (`BoundVar`, name-free); free occurrences keep stable ids; the only
transient id was the binder's, now excluded ⇒ `exact_key` is run-stable AND alpha-canonical.

### FIX-B — `x # N` guards (closes #1)
InNew/OutNew/OpenNew/AmbNew move the prefix name `N` under `new^x`; the equations guard `x # P` only,
under-guarded vs the standard `x ∉ fn(N)`. The handler ADDITIONALLY checks `x # N` (binder fresh in the
name) before floating, via the generated `is_fresh` over `N`. If `x ∈ fn(N)`, do not float (the congruence
genuinely does not apply). More correct than the equation/`run_ascent`; capturing terms documented in the
negative-pin bucket.

### FIX-C — bounded-honest composition (closes #2)

> **Superseded by the shipped implementation.** During implementation the bounded
> `float↔AC` loop below collapsed to a single float-once pass: floating `new`
> binders to a canonical prefix is idempotent, so a second round is never needed.
> The shipped, capture-safe mechanism is documented in
> [`11-binder-congruence-handler.md`](../11-binder-congruence-handler.md) and proven
> in `AmbientBinderHandler.v`. The loop is retained here as the design-derivation
> record (see the [sub-suite README](README.md), which also notes this collapse).

The float↔AC loop is BOUNDED and HONEST, not a claimed-perfect fixpoint:
```
T := input
for round in 0..MAX_FLOAT_ROUNDS:
    T1 := binder_congruence_nf(T)          // moniker: float new's out (FIX-B guards), canonical order (FIX-A)
    (P*, S) := peel_outer_new_prefix(T1)
    (S_roots, ac_completeness) := ac_saturate_and_extract(S)   // in-engine P4; CARRIES SaturationOutcome
    T2roots := { rewrap(P*, S') for S' in S_roots }            // FIX-D fans prefixes
    if set_eq_by_exact_key(T2roots, {T}):  converged := true; break
    T := canonical_join(T2roots)
completeness := Complete  iff (converged AND ac_completeness == Converged)  else BoundedByCycleCut
```
The inner AC `SaturationOutcome::{IterationLimit,NodeLimit}` (`rules.rs:163-169`) is propagated: a truncated
AC sub-run forces `BoundedByCycleCut` even if the outer `term_eq` coincidentally holds. No joint
termination proof is claimed; honesty about the bound IS the guarantee (Mandate-aligned: cyclic spaces stay
cycle-bounded). `binder_nf_idempotent` (a second float changes nothing) holds because FIX-A makes the
canonical NF a true fixpoint of the float.

### FIX-D — ambiguity fanning across the seam (closes #4)
Re-wrap fans `S_roots` into the full set of valid prefixed NFs (distinct extrusion orders → distinct
`Ambiguous` roots), never collapsing to a single `P*`. Dedup by `exact_key` (now canonical via FIX-A) is a
sound identity-dedup, never a weight-prune (all weights "0", `lib.rs:190`). Ambiguity preserved end-to-end.

### FIX-E — honest completeness channel (closes #5)
Add a completeness channel so the native seam reports the real value instead of hardcoding `Complete`:
- Extend the native handler's return (and/or `RewriteSeed` `language.rs:648-662`) with a
  `RuntimeDovetailCompleteness`.
- `complete_native_dovetail_report_for_language` (`lib.rs:132-210`) reads it and sets the report's
  completeness at `:204` instead of the hardcoded `Complete`.
Contract change, mechanical. Backstopped by the Rocq `report_complete_iff_both_converge`.

## 2. The NativeHandler algorithm (moniker, capture-safe, per equation)
`float_one(ctx, PNew scope)`: `(x', body) = scope.unbind()` (fresh x', open body) → structural move of ctx
around `body` (with FIX-B `x' # N` check for prefix equations) → `Scope::new(Binder(x'), moved)` (re-close).
- InNew/OutNew/OpenNew/AmbNew: float the inner `new^x` over the prefix `Prefix N _`, iff `x' # N` AND
  `x' # P` (the latter vacuous post-open).
- ScopeExtrusion: float the member `new^x` over the rest-bag, iff `rest.iter().all(|m| is_fresh(x', m))`
  (FULL-union multiset scan, no representative shortcut).
- NewComm: order the floated `new`-prefix by the FIX-A alpha-canonical `Scope` Ord (run-stable).
Termination of the float alone: each float strictly reduces Σ(new depth); O(n²); canonical sort `⇒` unique NF.
Witnesses do NOT capture: `new^z.in(z,new^x.0)` (re-close → z=`Bound{1,0}`); `new(x, x[0])` (FIX-B blocks
AmbNew since `x ∈ fn(N)`).

## 3. Plug-in seam + disposition gate (E)
Generated `try_direct_eval` override for Ambient (BEFORE the unsupported list,
`target/generated/ambient/dovetail_report.rs:25-40`; seam `lib.rs:132-210`), alt-preserving (maps over
`Ambiguous` like `normalize_term` `language_trait_impl.rs:109-124`), returns `Some(result, completeness)`
iff progress else `None` (fail-closed preserved). New generator `macros/src/gen/runtime/binder_congruence.rs`.
GATE at codegen by `has_binder_equations && has_no_host_disposition`: Ambient (no host) ⇒ emitted; rhocalc
(`Extrude` dispositioned `RhoNativeJoin`, `backend.rs:23-46`, `guard_quality.rs:131`) ⇒ NOT emitted, stays
host-routed. Keep `premise_supported(Freshness)=>false` (`dovetail_report.rs:404`) AND Rocq
`GPremFreshness=>false` (`GeneratedReportCompiler.v:90`) UNCHANGED — the handler is gated by disposition,
NOT by the generic premise switch. NEW regression `rhocalc_dovetail_report_stays_host_routed_for_extrude`.

## 4. Zero-admission Rocq — `dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v`
Imports Stdlib + `Requirements.MeTTaILRewriteCoverage` only (NO `RhocalcAstLowering.v`). Model
`eterm := EVarF nat | EVarB nat nat | EPrefix nat eterm | EBind eterm | EPar (list eterm)` with
`open`/`close`/`free_vars` mirroring moniker.
- T1 `float_preserves_denotation` (capture-safety, close∘open round-trip) + `from_parts_unsafe_captures`
  (PROVES run_ascent unsound on the witness — the negative pin's formal twin).
- T1' `ambnew_requires_fresh_name` (FIX-B): floating a prefix is denotation-preserving ONLY if `x # N`;
  exhibits the capture when `x ∈ fn(N)`.
- T2 `fresh`=free_vars-absence, `free_vars_no_bound_leak`, `fresh_bag_complement` (⊇/multiset; NO
  filter_adjust).
- T3 `binder_key_alpha_canonical` (FIX-A): the (body+arity)-hash is invariant under binder renaming and
  injective on alpha-classes ⇒ `exact_key` run-stable; `binder_nf_idempotent`.
- T4 coverage reuse `apply every_requirement_constructor_is_covered` (no new constructors).
- T5 disposition routing `rhocalc_stays_host_routed` / `ambient_native_handler_emitted`; keeps
  `GPremFreshness=false` so the existing `supported_premises_are_only_congruence` proof is untouched.
- T6 `report_complete_iff_both_converge` (FIX-C/E honesty).

## 5. Staged increments (smallest-verifiable-first; each = code + Rocq + test; FOREGROUND)
- **Inc 0 — Negative pin + alpha-canonical identity (FIX-A) + capture demo.** FIX-A across semantic_hash /
  e-graph label / Scope::cmp. Test: `new(x,x)` and `new(y,y)` get EQUAL `exact_key`; `dovetail_report_for`
  twice ⇒ byte-identical keys; `new(x,z)≢new(x,w)`. Negative pin: a hand-written moniker reference and
  `run_ascent` DISAGREE on `new^z.in(z,new^x.0)` (run_ascent captures). Rocq T3 + T1's
  `from_parts_unsafe_captures`. (Valuable standalone — fixes a latent identity bug.)
- **Inc 1 — NativeHandler float (FIX-B), no AC.** `binder_congruence.rs` + `try_direct_eval` override,
  gated. Rocq T1,T1',T2,T4. Tests: capture witnesses do NOT capture; `new(x,x)≡new(y,y)`; AmbNew blocked
  when `x∈fn(N)`; gold-moniker-reference equality on a congruence corpus.
- **Inc 2 — Bounded-honest composition (FIX-C) + completeness channel (FIX-E) + fanning (FIX-D).** Wire the
  float↔AC loop; thread `RuntimeDovetailCompleteness` through the seam. Rocq T6 + `binder_nf_idempotent`.
  Tests: `{open(n,0)|n[0]}` reduces; an OpenRule that re-exposes a `new` re-floats and converges; a
  non-terminating term ⇒ `BoundedByCycleCut` (NOT `Complete`); a truncated inner AC ⇒ `BoundedByCycleCut`;
  ambiguity ≥2 roots across the seam; determinism (twice `⇒` identical root sets).
- **Inc 3 — Disposition gate + rhocalc pin + flip the gate test.** Rocq T5. `rhocalc_dovetail_report_stays_
  host_routed_for_extrude`; flip `ambient_dovetail_flip.rs` `expect_err`→`expect`.
- **Inc 4 — Differential oracle on the NON-capturing corpus** (gated `ambient+dovetail-codegen+oracle-
  ascent`), clear var-cache once; assert ContentKey sets equal; plus the negative pin from Inc 0.

## 6. Honest scope statement
The moniker congruence NF is sound + total; AC reduction is Turing-complete so some terms legitimately
report `BoundedByCycleCut` (honest, not a lie). No unsound in-engine binder rewrite; no `Complete` that
lies. FIX-A is a genuine correctness fix beyond Ambient (binder identity was non-alpha-canonical). The only
semantic divergence from the legacy reference is intentional and documented: v4 is capture-SAFE where
`run_ascent` is capture-unsound, and v4 adds the `x # N` guard the equations omit.

## 7. Biggest residual threat (for the final red-team)
FIX-A changes binder `exact_key`/`content_key` for EVERY language's generated code, even though only
Ambient consumes it at runtime today. Threat: a hidden consumer (a test pinning a binder `exact_key`, a
cross-language report, the rho-bridge fingerprint) depends on the OLD non-canonical key and breaks. Mitigation:
grep every `exact_key`/`semantic_hash`/`content_key` consumer + every binder-bearing test BEFORE landing
FIX-A; run the full op-suite + rho-bridge + formal gates; FIX-A is Inc 0 precisely so any breakage surfaces
first, in isolation, before the handler is built on top.
