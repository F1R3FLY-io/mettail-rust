# Ambient Binder + Freshness Lowering for the Dovetail Flip — Converged Design (v4)

**Status:** design CONVERGED via plan→red-team iteration (v1→v4, 3+ adversarial rounds);
implementation **COMPLETE** (Inc 0–4, committed). Branch `feature/wfst-architecture`. Part of P5b (Ambient flip).

> **Read this as the design-derivation record** — how the design was reached,
> including superseded iterations and refuted approaches (kept deliberately, per the
> project's "document even what does not work" rule). The authoritative description
> of the *implemented* mechanism is the published
> [Binder-Congruence Handler](../11-binder-congruence-handler.md). Two simplifications
> were discovered during implementation and are reflected there but not below: FIX-B
> *blocking* proved **unnecessary** (moniker `unbind` freshening makes the float always
> capture-safe, so there is nothing to block), and the float↔AC fixpoint loop collapses
> to **float-once** (a bottom-up float moves every `new` to the top; the AC rules add
> none back). §1's present-tense "FAILS CLOSED on Ambient" describes the *pre-flip*
> state this work removed; `ambient_dovetail_flip.rs` now asserts **Complete** reports.

This document is the durable record of the design and its derivation, sufficient to reconstruct it
from scratch. The blow-by-blow red-team ledgers live alongside in this directory.

## 1. Problem

The generated Dovetail report compiler FAILS CLOSED on Ambient (`languages/tests/ambient_dovetail_flip.rs`):
its structural-congruence EQUATIONS carry the `PNew ^x` binder (`NewComm`) and freshness side conditions
(`ScopeExtrusion`, `InNew`/`OutNew`/`OpenNew`/`AmbNew`). Ambient's AC reduction RULES
(`InRule`/`OutRule`/`OpenRule`) already lower in-engine (P4). Unlike a process calculus (rhocalc/guarded_rho,
whose binders/COMM delegate to host RSpace via `RhoNativeJoin`), Ambient has NO host: its binders + freshness
must be handled before it can flip. The six equations (`languages/src/ambient.rs:30-35`):

```
NewComm        . (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P))
ScopeExtrusion . | x # ...rest | (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}))
InNew/OutNew/OpenNew/AmbNew . | x # P | (Prefix N (PNew ^x.P)) = (PNew ^x.(Prefix N P))
```

## 2. Why the obvious approach (lower binders in-engine) is UNSOUND — the derivation

Three design iterations were adversarially refuted before convergence:

- **v1/v2 (lower binders to a de-Bruijn e-graph representation).** REFUTED. The e-graph hashconses
  `db::(scope,binder)` leaves by coordinate, so the SAME leaf is shared across unrelated binder contexts
  at different depths. Any equation that re-homes a subterm across a binder (changing its depth) needs a
  de-Bruijn index SHIFT, which has no finite confluent definition over a shared-leaf e-class DAG without an
  e-class-analysis framework (which `dovetail` does not have). Capture witness:
  `new^w.{new^x.P, w[0]}` → ScopeExtrusion → `w`'s `db::0.0` leaf re-homed under `new^x` (now denotes `x`)
  ⇒ bound-variable capture; the freshness guard `x # rest` PASSES so offers no protection.
- **STRONGER finding:** ALL SIX equations are depth/coordinate-changing (NewComm swaps binders ⇒ body
  `db::0↔db::1`; ScopeExtrusion moves `rest`; the four prefix equations move the name `N` under `new^x` —
  witness `new^z.in(z,new^x.0)` captures `z`). So none can be a sound in-engine rewrite over shared leaves.
- This matches the campaign's **disposition-first decision rule**: in-engine iff *ambiguous AND host-less*;
  the binder equations are DETERMINISTIC congruences ⇒ they are a **NativeHandler** disposition, not
  in-engine. Only the genuinely-ambiguous AC reduction stays in-engine (P4).

## 3. The verified architecture (v3 Part A — VERIFIED airtight)

**Binder congruences → a moniker-based NativeHandler** using moniker's capture-safe primitives:
`Scope::unbind` (freshens the binder to a new `FreeVar`, opens the body) → structural move on the OPEN term
→ `Scope::new` (re-closes, recomputing de-Bruijn coordinates LOCALLY via `close_term`'s depth increment).
This never shares leaves across binder contexts, so it cannot capture.

**Key finding (verified end-to-end against generated code):** the legacy `run_ascent` reference is ITSELF
capture-unsound on these equations. The generated Ambient `ascent.rs` DOES emit all six equations
(`generate_equation_rules`, NOT the eqrel-congruence path which skips binders), but reconstructs subterms
with `Scope::from_parts_unsafe` + structural `normalize()` (9 `from_parts_unsafe`, 0 `Scope::new` in the
generated `normalize.rs`) — NO coordinate re-close. So `run_ascent` on `new^z.in(z,new^x.0)` produces a
CAPTURED normal form. Consequence: the differential-vs-Ascent oracle is valid ONLY on a non-capturing
corpus; the trustworthy gold reference is a hand-written moniker `unbind`/`free_vars`/`Scope::new` handler
(which IS the NativeHandler), plus a NEGATIVE pin documenting that `run_ascent` and the moniker reference
disagree on capturing witnesses.

**Composition with in-engine AC** (`InRule`/`OutRule`/`OpenRule`): a BOUNDED-HONEST fixpoint — float the
`new`s outward (native), peel the outer `new`-prefix, AC-saturate the soup in-engine (ambiguity-preserving),
re-wrap, repeat until `term_eq` fixpoint OR a bound (`max_float_rounds`/`max_iters`/`max_nodes`) ⇒
`BoundedByCycleCut` (NOT `Complete`). Sound per round by `NewCong` closure (reducing `S` then re-wrapping
`P*` equals reducing `new P*.S`). AC reduction is Turing-complete, so some terms legitimately report
`BoundedByCycleCut` — honest, not a lie.

## 4. The five fixes (round-3 red-team; all CLOSED in v4)

- **FIX-A (alpha-canonical binder identity) — the gating fix.** moniker `unique_id` (a process-global
  counter freshened by every `unbind`, never reset by `clear_var_cache`) leaks into binder identity,
  making `exact_key`/`content_key` RUN-VARYING (so dedup over-counts and the WPDA seed is unstable). The
  fix makes the SEMANTIC identity path alpha-canonical (hash the de-Bruijn body + binder ARITY, exclude the
  binder `FreeVar`). **Implementation-depth discovery (beyond the red-team):** the leak is NOT only the
  binder arm of `semantic_hash` (`macros/src/gen/term_ops/semantic_hash.rs:525,577`) — Ambient's `PPar` is a
  `HashBag(Proc)` and the COLLECTION arm (`:417-420,:461-464`) hashes elements via std `Hash`, which routes
  binder-bearing elements through the structural `Hash for Scope` (`runtime/src/binding.rs:210`) and leaks
  `unique_id` there too. `Scope`'s std `Hash`/`Eq`/`Ord` are deliberately STRUCTURAL (for Ascent/HashMap)
  and internally consistent — they must NOT be changed (would break the `Hash`/`Eq` contract). So FIX-A
  must canonicalize the SEMANTIC path only. Two candidate realizations (decide at implementation):
  (A-global) make `semantic_hash` alpha-canonical through binders AND collections (order-independent
  multiset combine; broad, performance-sensitive); (A-local) the handler canonically re-numbers its
  output's binder `unique_id`s (alpha-rename to a canonical de-Bruijn-position form) so the existing
  structural hash becomes deterministic + alpha-canonical with NO global infra change. A-local is
  preferred if moniker supports canonical `FreeVar` construction; investigate first.
- **FIX-B (`x # N` guard).** `InNew`/`OutNew`/`OpenNew`/`AmbNew` move the name `N` under `new^x`; the
  equations guard `x # P` only (under-guarded vs the standard `x ∉ fn(N)`). The handler ALSO checks `x # N`
  before floating. More correct than the equations/`run_ascent`; documented divergence.
- **FIX-C (bounded-honest composition).** Propagate the inner AC `SaturationOutcome` so a truncated AC run
  is NEVER reported `Complete`; bound the float↔AC loop; report `BoundedByCycleCut` honestly.
- **FIX-D (ambiguity fanning).** Re-wrap fans the AC roots into all valid prefixed NFs; dedup by the
  now-canonical `exact_key` (FIX-A) is identity-dedup, never a weight-prune (weights all "0").
- **FIX-E (completeness channel).** Thread a real `RuntimeDovetailCompleteness` through the native seam
  (`dovetail-runtime/src/lib.rs:204` currently hardcodes `Complete`); via the `try_direct_eval`
  return, NOT `RewriteSeed`.

## 5. Disposition gate
The handler is generated for a language iff `has_binder_equations && has_no_host_disposition`. Ambient (no
host) ⇒ emitted; rhocalc's `Extrude` (dispositioned `RhoNativeJoin`) ⇒ NOT emitted, stays host-routed.
`premise_supported(Freshness)=>false` stays UNCHANGED (the handler is disposition-gated, not premise-gated).
Regression: `rhocalc_dovetail_report_stays_host_routed_for_extrude`. Seam: the `try_direct_eval` override is
generated in the `Language`-trait generator (`macros/src/gen/runtime/language.rs:3651`).

## 6. Zero-admission Rocq — `dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v`
Model `eterm := EVarF | EVarB | EPrefix | EBind | EPar` with moniker-faithful `open`/`close`/`free_vars`.
Theorems: T1 `float_preserves_denotation` + `from_parts_unsafe_captures` (proves run_ascent unsound on the
witness); T1' `ambnew_requires_fresh_name` (FIX-B); T2 `fresh = free_vars-absence`, `fresh_bag_complement`;
T3 `binder_key_alpha_canonical` + `binder_nf_idempotent` (FIX-A; faithful to the artifact ONLY after FIX-A
lands — hence FIX-A is Inc 0); T4 coverage reuse (`every_requirement_constructor_is_covered`, no new
constructors); T5 disposition routing (keeps `GPremFreshness=false` so the existing
`supported_premises_are_only_congruence` proof is untouched); T6 `report_complete_iff_both_converge`.

## 7. Increments (smallest-verifiable-first; each = code + Rocq + test; FOREGROUND)
- **Inc 0** — FIX-A (alpha-canonical binder identity) + the run_ascent negative pin. Standalone correctness
  fix; sequenced first to isolate the blast radius. Tests: `new(x,x)≡new(y,y)` equal `exact_key`;
  `dovetail_report_for` twice ⇒ identical keys; `new(x,z)≢new(x,w)`. Gates: full op-suite across binder
  languages (calculator/lambda/rhocalc/guarded_rho/ambient) + rho-bridge + formal.
- **Inc 1** — NativeHandler float (FIX-B), no AC. Rocq T1/T1'/T2/T4. Capture witnesses do NOT capture;
  gold-moniker-reference equality.
- **Inc 2** — bounded-honest composition (FIX-C) + completeness channel (FIX-E) + fanning (FIX-D). Rocq
  T6 + idempotence. Non-terminating term ⇒ `BoundedByCycleCut`; ambiguity ≥2 roots; determinism pin.
- **Inc 3** — disposition gate + rhocalc host-routed pin + flip `ambient_dovetail_flip.rs`. Rocq T5.
- **Inc 4** — differential oracle on the NON-capturing corpus + the negative pin.

## 8. Honest scope
The moniker congruence NF is sound + total; AC reduction is Turing-complete so some terms legitimately
report `BoundedByCycleCut`. No unsound in-engine binder rewrite; no `Complete` that lies. FIX-A is a genuine
correctness fix beyond Ambient (binder identity was non-alpha-canonical system-wide). The only semantic
divergence from the legacy reference is intentional + documented: v4 is capture-SAFE where `run_ascent` is
capture-unsound, and adds the `x # N` guard the equations omit.
